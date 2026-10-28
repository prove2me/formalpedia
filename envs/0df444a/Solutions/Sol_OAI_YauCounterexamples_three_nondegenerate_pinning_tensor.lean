-- Prove2me | solution 1 for OAI.YauCounterexamples.three_nondegenerate_pinning_tensor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:46:03.139466+00:00
-- url     : https://prove2.me/submissions/98bb3c5e-2bb5-4b97-970f-0d9af0111dd7

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A011
import Theorems.Thm_OAI_YauCounterexamples_three_rank_separating_tensor

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmetricFormsNondegenerate
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix Function
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_one_zero_perturbation (a : ι → ℝ) (i : ι)
    (hzero : a i = 0) (ha : ∀ j, j ≠ i → a j ≠ 0)
    (B : Matrix ι ι ℝ) (hB : B i i ≠ 0) :
    ∃ t : ℝ, (diagonal a + t • B).det ≠ 0 := by
  let d : ι → ℝ := Function.update a i 1
  have hd (j : ι) : d j ≠ 0 := by
    by_cases hj : j = i
    · subst j; simp [d]
    · simpa [d, hj] using ha j hj
  have hdet : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  have hv : B i = ∑ j, (B i j / d j) • (diagonal d) j := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, diagonal_apply]
    rw [Finset.sum_eq_single k]
    · rw [ite_eq_left rfl, div_mul_cancel₀ _ (hd k)]
    · intro b _ hb; rw [ite_eq_right hb, mul_zero]
    · simp
  have hbase : ((diagonal a).updateRow i (B i)).det ≠ 0 := by
    have he : (diagonal a).updateRow i (B i) = (diagonal d).updateRow i (B i) := by
      ext j k
      by_cases hj : j = i
      · subst j; simp
      · simp only [Matrix.updateRow_apply, ite_eq_right hj, diagonal_apply]
        simp [d, hj]
    rw [he, hv, Matrix.det_updateRow_sum]
    simpa [d] using mul_ne_zero hB hdet
  have hc : Continuous (fun t : ℝ => ((diagonal a + t • B).updateRow i (B i)).det) := by
    apply Continuous.matrix_det
    apply continuous_pi; intro j
    apply continuous_pi; intro k
    by_cases hj : j = i
    · subst j; simpa using continuous_const (y := B i k)
    · simp only [Matrix.updateRow_apply, ite_eq_right hj]
      fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ((diagonal a + t • B).updateRow i (B i)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using hbase)
  have hn' : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ((diagonal a + t • B).updateRow i (B i)).det ≠ 0 :=
    hn.filter_mono nhdsWithin_le_nhds
  have hz : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := eventually_mem_nhdsWithin
  obtain ⟨t,ht,ht0⟩ := (hn'.and hz).exists
  refine ⟨t, ?_⟩
  have hr : (diagonal a + t • B) i = t • B i := by
    ext j
    simp [diagonal_apply, hzero]
  have he : (diagonal a + t • B).det =
      t * ((diagonal a + t • B).updateRow i (B i)).det := by
    conv_lhs => rw [← Matrix.updateRow_eq_self (diagonal a + t • B) i, hr]
    exact Matrix.det_updateRow_smul _ _ _ _
  rw [he]
  exact mul_ne_zero ht0 ht

theorem symmetric_pencil_nondegenerate
    (L : Submodule ℝ (Matrix ι ι ℝ))
    (hL : ∀ A ∈ L, A.IsHermitian)
    (hsep : ∀ v : ι → ℝ, v ≠ 0 → ∃ B ∈ L, v ⬝ᵥ (B *ᵥ v) ≠ 0) :
    ∃ A ∈ L, A.det ≠ 0 := by
  let S : Set ℕ := {r | ∃ A ∈ L, A.rank = r}
  have hSf : S.Finite := (Set.finite_Iic (Fintype.card ι)).subset (by
    rintro r ⟨A,_,rfl⟩
    exact A.rank_le_card_width)
  obtain ⟨r,hr,hrmax⟩ := hSf.exists_maximal ⟨0, 0, L.zero_mem, by simp⟩
  obtain ⟨A,hAL,hAr⟩ := hr
  have hmax (B : Matrix ι ι ℝ) (hBL : B ∈ L) : B.rank ≤ A.rank := by
    by_contra hb
    have hle : r ≤ B.rank := by omega
    have := hrmax ⟨B,hBL,rfl⟩ hle
    omega
  have hA := hL A hAL
  by_cases hdet : A.det ≠ 0
  · exact ⟨A,hAL,hdet⟩
  have heig : ∃ i, hA.eigenvalues i = 0 := by
    by_contra! hh
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hh i)
  obtain ⟨i,hi⟩ := heig
  let U := hA.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star U)
  have hFA : F A = diagonal hA.eigenvalues := by
    simpa [F,U] using hA.conjStarAlgAut_star_eigenvectorUnitary
  let v : ι → ℝ := fun j => U j i
  have hv : v ≠ 0 := by
    intro hz
    have hh : hA.eigenvectorBasis i = 0 := by
      apply PiLp.ext; intro j
      exact congrFun hz j
    exact hA.eigenvectorBasis.toBasis.ne_zero i hh
  obtain ⟨B,hBL,hB⟩ := hsep v hv
  have hFB : F B i i ≠ 0 := by
    convert hB using 1
    all_goals try with_reducible_and_instances rfl
    simp only [F, Unitary.conjStarAlgAut_star_apply, Matrix.mul_apply,
      Matrix.star_apply, star_trivial, dotProduct, mulVec, v]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  let J := Option {j // hA.eigenvalues j ≠ 0}
  let e : J → ι := fun j => j.elim i Subtype.val
  have hei : Function.Injective e := by
    intro j k he
    cases j with
    | none => cases k with
      | none => rfl
      | some k =>
        have hk : i = k.val := he
        exact (k.property (hk ▸ hi)).elim
    | some j => cases k with
      | none =>
        have hj : j.val = i := he
        exact (j.property (hj ▸ hi)).elim
      | some k => exact congrArg some (Subtype.ext he)
  have hae (j : J) (hj : j ≠ none) : hA.eigenvalues (e j) ≠ 0 := by
    cases j with
    | none => exact (hj rfl).elim
    | some j => exact j.property
  obtain ⟨t,ht⟩ := diagonal_one_zero_perturbation
    (fun j : J => hA.eigenvalues (e j)) none hi hae
    ((F B).submatrix e e) hFB
  have hminor : (F (A + t • B)).submatrix e e =
      diagonal (fun j : J => hA.eigenvalues (e j)) + t • (F B).submatrix e e := by
    rw [map_add, map_smul, hFA, Matrix.submatrix_add, Matrix.submatrix_smul]
    change (diagonal hA.eigenvalues).submatrix e e + t • (F B).submatrix e e = _
    rw [Matrix.submatrix_diagonal _ _ hei]
    rfl
  have hrank (C : Matrix ι ι ℝ) : (F C).rank = C.rank := by
    simp only [F, Unitary.conjStarAlgAut_star_apply]
    simp [-isUnit_iff_ne_zero, ← Unitary.coe_star]
  have hbig : Fintype.card J ≤ (A + t • B).rank := by
    have hnt : ((F (A + t • B)).submatrix e e).det ≠ 0 := by rw [hminor]; exact ht
    rw [← hrank, ← Matrix.rank_of_det_ne_zero hnt]
    exact Matrix.rank_submatrix_le _ _ _
  have hsmall := hmax (A + t • B) (L.add_mem hAL (L.smul_mem t hBL))
  rw [hA.rank_eq_card_non_zero_eigs] at hsmall
  have hcard : Fintype.card J = Fintype.card {j // hA.eigenvalues j ≠ 0} + 1 :=
    Fintype.card_option
  omega

end


open LinearMap
open scoped Matrix

theorem symmetric_forms_nondegenerate
    {P W : Type*} [AddCommGroup P] [Module ℝ P]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : P →ₗ[ℝ] LinearMap.BilinForm ℝ W)
    (hB : ∀ p x y, B p x y = B p y x)
    (hsep : ∀ w : W, w ≠ 0 → ∃ p, B p w w ≠ 0) :
    ∃ p, (B p).Nondegenerate := by
  classical
  let b := Module.finBasis ℝ W
  let L := ((LinearMap.BilinForm.toMatrix b).toLinearMap.comp B).range
  have hs : ∀ A ∈ L, A.IsHermitian := by
    rintro A ⟨p,rfl⟩
    rw [Matrix.isHermitian_iff_isSymm]
    exact (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm b).mpr ⟨hB p⟩
  have hh : ∀ v : Fin (Module.finrank ℝ W) → ℝ, v ≠ 0 →
      ∃ A ∈ L, v ⬝ᵥ (A *ᵥ v) ≠ 0 := by
    intro v hv
    have hw : b.equivFun.symm v ≠ 0 := by
      intro hz
      apply hv
      apply b.equivFun.symm.injective
      exact hz.trans (map_zero b.equivFun.symm).symm
    obtain ⟨p,hp⟩ := hsep _ hw
    refine ⟨(B p).toMatrix b,⟨p,rfl⟩,?_⟩
    simpa only [LinearMap.BilinForm.dotProduct_toMatrix_mulVec] using hp
  obtain ⟨A,⟨p,rfl⟩,hA⟩ := symmetric_pencil_nondegenerate L hs hh
  exact ⟨p,(LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr hA⟩

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_PositiveIntegral
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction CompactlySupported
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

lemma mean_eq_volumeIntegral (f : M → ℝ) (hf : Continuous f) :
    I.mean g f = ∫ x, f x ∂I.volumeMeasure g := by
  let F : C_c(M,ℝ) := ⟨⟨f,hf⟩,HasCompactSupport.of_compactSpace f⟩
  exact (RealRMK.integral_rieszMeasure (I.positiveIntegral g) F).symm

end MetricIntegralAtlas
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearTransverse
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma bilinearTransverse_apply (G : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) :
    bilinearTransverse G a b = b - ((G a a)⁻¹ * G a b) • a := by
  simp [bilinearTransverse,smul_smul]
lemma bilinearTransverse_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) (a b c : E) :
    G (bilinearTransverse G a b) c = G b (bilinearTransverse G a c) := by
  simp only [bilinearTransverse_apply,map_sub,map_smul,sub_apply,
    smul_apply,smul_eq_mul]
  rw [hs b a]; ring
lemma bilinearPinning_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ a b, G a b = G b a) (a b v w : E) :
    G (bilinearPinning G a b v) w = G v (bilinearPinning G a b w) := by
  simp only [bilinearPinning,sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,map_sub,map_smul,smul_eq_mul]
  rw [bilinearTransverse_selfAdjoint G hs a v w,hs v (bilinearTransverse G a b)]
  ring
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_SupportedPinningTensor
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma supportedPinningTensor_eq (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M) :
    supportedPinningTensor g u v χ x =
      χ x • bilinearPinning (E := E) (g.inner x) (metricGradient g u x) (metricGradient g v x) := rfl

lemma supportedPinningTensor_selfAdjoint (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (a b : TangentSpace 𝓘(ℝ,E) x) :
    g.inner x (supportedPinningTensor g u v χ x a) b =
      g.inner x a (supportedPinningTensor g u v χ x b) := by
  rw [supportedPinningTensor_eq]
  change (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
      (χ x • bilinearPinning (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
        (metricGradient g u x) (metricGradient g v x) (show E from a)) (show E from b) =
    (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x) (show E from a)
      (χ x • bilinearPinning (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
        (metricGradient g u x) (metricGradient g v x) (show E from b))
  erw [map_smul, smul_apply, map_smul]
  change χ x * _ = χ x * _
  exact congrArg (fun r : ℝ => χ x * r)
    (bilinearPinning_selfAdjoint (E := E) (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
      (g.symm x) (metricGradient g u x) (metricGradient g v x) a b)

lemma supportedPinningTensor_zero (g : SmoothMetric E M) (u v χ : M → ℝ) (x : M)
    (hχ : χ x = 0) : supportedPinningTensor g u v χ x = 0 := by
  simp only [supportedPinningTensor_eq,hχ,zero_smul]
  rfl

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_RestrictedPinningPencil
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)
variable {u : M → ℝ} {U : Set M}

omit [T2Space M] in
lemma pinningEnergyPencil_symmetric (K : pinningTensorSpace g u U)
    (a b : RealSmoothFunctions E M) :
    pinningEnergyPencil I g K a b = pinningEnergyPencil I g K b a := by
  change I.mean g _ = I.mean g _
  congr 1
  funext x
  exact (g.symm x _ _).trans (K.property.2.1 x _ _)
end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeManifold_preconnected : PreconnectedSpace ThreeManifold := by
  let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [Euclidean,finrank_euclideanSpace]) (0:Euclidean 3) 1)
  let : PreconnectedSpace Circle := inferInstance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
end


section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
attribute [local instance] OAI.YauCounterexamples.instMeasurableSpaceThreeManifold_1
local instance instBorelSpaceThreeManifold_1 : BorelSpace ThreeManifold := ⟨rfl⟩
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem three_nondegenerate_pinning_tensor_oai
    (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
    (g : SmoothMetric ThreeModel ThreeManifold)
    {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
    (u : RealSmoothFunctions ThreeModel ThreeManifold)
    (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
    (hG : ∀ p∈S, 0 < coordinateGradientPair g u u p)
    (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    (σ : W →ₗ[ℝ] RealSmoothFunctions ThreeModel ThreeManifold)
    (hσ : Injective σ)
    (hσe : ∀ w p, -laplaceBeltrami g (σ w) p = Λ*σ w p)
    (hσo : ∀ w, I.mean g (fun x => σ w x*u x) = 0) :
    ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
      S,
      (restrictedPinningPencil I g σ K).Nondegenerate := by
  let := threeManifold_preconnected
  apply symmetric_forms_nondegenerate (restrictedPinningPencil I g σ)
  · intro K v w
    exact pinningEnergyPencil_symmetric I g K (σ v) (σ w)
  · intro w hw
    have hv : (σ w : ThreeManifold → ℝ) ≠ 0 := by
      intro hz
      apply hw
      apply hσ
      rw [map_zero]
      exact DFunLike.ext _ _ (congrFun hz)
    have ho : ∫ x, σ w x*u x ∂I.volumeMeasure g = 0 := by
      exact (I.mean_eq_volumeIntegral g (fun x => σ w x*u x)
        ((σ w).contMDiff.continuous.mul u.contMDiff.continuous)).symm.trans (hσo w)
    obtain ⟨χ,hχ,hK,htr,hku,hpos⟩ := three_rank_separating_tensor
      (I.volumeMeasure g) g u.contMDiff (σ w).contMDiff hΛ hue (hσe w) hS hG hrank hv ho
    let K : pinningTensorSpace g (u : ThreeManifold → ℝ)
        S :=
      ⟨supportedPinningTensor g u (σ w) χ,
        hK, supportedPinningTensor_selfAdjoint g u (σ w) χ,htr,hku,by
          intro x hx
          apply supportedPinningTensor_zero
          by_contra hn
          exact hx (hχ (subset_tsupport _ hn))⟩
    refine ⟨K,ne_of_gt ?_⟩
    change 0 < I.mean g (fun x => g.inner x (metricGradient g (σ w) x)
      (supportedPinningTensor g u (σ w) χ x (metricGradient g (σ w) x)))
    rw [I.mean_eq_volumeIntegral g _
      (contMDiff_tensorEnergy g _ hK (σ w).contMDiff (σ w).contMDiff).continuous]
    exact hpos

end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.three_nondegenerate_pinning_tensor_oai.{u_1} := @OAI.YauCounterexamples.three_nondegenerate_pinning_tensor_oai.{u_1}
