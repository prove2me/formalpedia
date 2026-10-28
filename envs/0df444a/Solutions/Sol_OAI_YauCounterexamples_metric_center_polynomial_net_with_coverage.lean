-- Prove2me | solution 1 for OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:35:58.703422+00:00
-- url     : https://prove2.me/submissions/3abb1ab1-16d1-45c2-8332-4cc158466535

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GridPoint
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
namespace YauCounterexamples

theorem gridPoint_cover (d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (x : Fin d → ℝ) (hx : ‖x‖ ≤ (m : ℝ) * δ) :
    ∃ k : Fin d → Fin (2 * m + 1), dist x (gridPoint d m δ k) ≤ δ := by
  have hcoord (j : Fin d) : |x j| ≤ (m : ℝ) * δ :=
    (norm_le_pi_norm x j).trans hx
  have hy0 (j : Fin d) : 0 ≤ x j / δ + (m : ℝ) := by
    have hh : -(m : ℝ) ≤ x j / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [(abs_le.mp (hcoord j)).1])
    linarith
  have hy2 (j : Fin d) : x j / δ + (m : ℝ) ≤ (2 * m : ℕ) := by
    have h := (abs_le.mp (hcoord j)).2
    have hh : x j / δ ≤ (m : ℝ) := (div_le_iff₀ hδ).mpr h
    push_cast
    linarith
  let k : Fin d → Fin (2 * m + 1) := fun j =>
    ⟨⌊x j / δ + (m : ℝ)⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (hy2 j))⟩
  refine ⟨k, ?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro j
  change |x j - δ * ((⌊x j / δ + (m : ℝ)⌋₊ : ℝ) - m)| ≤ δ
  have h := Nat.abs_sub_floor_le (hy0 j)
  have heq : x j - δ * ((⌊x j / δ + (m : ℝ)⌋₊ : ℝ) - m) =
      δ * (x j / δ + m - ⌊x j / δ + (m : ℝ)⌋₊) := by field_simp; ring
  rw [heq, abs_mul, abs_of_pos hδ]
  nlinarith

theorem gridPoint_card (d m : ℕ) :
    Fintype.card (Fin d → Fin (2 * m + 1)) = (2 * m + 1) ^ d := by simp

theorem recenter_finite_net {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (p : I → X) (K : Set X) (δ : ℝ)
    (hcover : ∀ x ∈ K, ∃ i, dist x (p i) ≤ δ) :
    ∃ t : Finset X, (↑t : Set X) ⊆ K ∧ t.card ≤ Fintype.card I ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ 2 * δ := by
  classical
  let A : Set I := {i | ∃ x ∈ K, dist x (p i) ≤ δ}
  let : Fintype A := Fintype.ofFinite A
  let q : A → X := fun i => i.property.choose
  have hq (i : A) : q i ∈ K ∧ dist (q i) (p i) ≤ δ := i.property.choose_spec
  refine ⟨Finset.univ.image q, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hq i).1
  · exact (Finset.card_image_le).trans (Fintype.card_le_of_injective (fun i : A => (i : I)) Subtype.val_injective)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    let j : A := ⟨i, x, hx, hi⟩
    refine ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    calc
      dist x (q j) ≤ dist x (p i) + dist (p i) (q j) := dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add hi (by simpa [dist_comm] using (hq j).2)
      _ = 2 * δ := by ring

theorem cube_subset_finite_net (d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (K : Set (Fin d → ℝ)) (hK : ∀ x ∈ K, ‖x‖ ≤ (m : ℝ) * δ) :
    ∃ t : Finset (Fin d → ℝ), (↑t : Set (Fin d → ℝ)) ⊆ K ∧
      t.card ≤ (2 * m + 1) ^ d ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ 2 * δ := by
  simpa only [gridPoint_card] using recenter_finite_net (gridPoint d m δ) K δ
    (fun x hx => gridPoint_cover d m δ hδ x (hK x hx))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma selfMetricFlat_invertible (g : SmoothMetric E E) (x : E) :
    (selfMetricFlat g x).IsInvertible := by
  rw [←localMetricFlat_self g x x]
  exact localMetricFlat_invertible g x x (mem_baseSet_trivializationAt E _ x)

lemma coordinateKoszul_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w z : E) :
    coordinateKoszul D v w z = (D v w z+D w v z-D z v w)/2 := by
  change (1/2 : ℝ) * (D v w z+D w v z-D z v w) = _
  ring

lemma metricChristoffel_pairing (g : SmoothMetric E E) (x v w z : E) :
    selfMetricFlat g x (metricChristoffel g x v w) z =
      (fderiv ℝ (selfMetricFlat g) x v w z+fderiv ℝ (selfMetricFlat g) x w v z-
        fderiv ℝ (selfMetricFlat g) x z v w)/2 := by
  have h := (selfMetricFlat_invertible g x).inverse_apply_eq.mp
    (show (selfMetricFlat g x).inverse (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x) v w) =
      metricChristoffel g x v w from rfl)
  exact (congrArg (fun l : E →L[ℝ] ℝ => l z) h.symm).trans (coordinateKoszul_apply _ _ _ _)

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
attribute [local instance] OAI.YauCounterexamples.metricFormNorm
attribute [local instance] OAI.YauCounterexamples.metricFormSpace
attribute [local instance] OAI.YauCounterexamples.metricTriNorm
attribute [local instance] OAI.YauCounterexamples.metricTriSpace
lemma contDiff_metricChristoffel (g : SmoothMetric E E) : ContDiff ℝ ∞ (metricChristoffel g) := by
  have hG := contDiff_selfMetricFlat g
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x hG.contDiffAt
  have hD := hG.fderiv_right (m := ∞) (by simp)
  have hDf : ContDiff ℝ ∞ (fun x => (fderiv ℝ (selfMetricFlat g) x).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp hD
  have hK : ContDiff ℝ ∞ (fun x => coordinateKoszul (fderiv ℝ (selfMetricFlat g) x)) :=
    (hD.add hDf |>.sub (contDiff_const.clm_comp hDf)).const_smul (1/2 : ℝ)
  exact (contDiff_const.clm_apply hGi).clm_comp hK

omit [FiniteDimensional ℝ E] in
lemma fderiv_selfMetricFlat_symm (g : SmoothMetric E E) (x v w z : E) :
    fderiv ℝ (selfMetricFlat g) x v w z = fderiv ℝ (selfMetricFlat g) x v z w := by
  have hd := (contDiff_selfMetricFlat g).differentiable (by simp)
  have he : (fun y => selfMetricFlat g y w z) = (fun y => selfMetricFlat g y z w) :=
    funext (fun y => selfMetricFlat_symm g y w z)
  have h := congrArg (fun f : E → ℝ => fderiv ℝ f x v) he
  have heval (w z : E) : fderiv ℝ (fun y => selfMetricFlat g y w z) x v =
      fderiv ℝ (selfMetricFlat g) x v w z := by
    rw [fderiv_clm_apply ((hd x).clm_apply (differentiableAt_const w))
        (differentiableAt_const z),
      fderiv_clm_apply (hd x) (differentiableAt_const w)]
    simp
  simpa only [heval] using h

lemma metricChristoffel_symm (g : SmoothMetric E E) (x v w : E) :
    metricChristoffel g x v w = metricChristoffel g x w v := by
  apply (selfMetricFlat_invertible g x).injective
  ext z
  rw [metricChristoffel_pairing,metricChristoffel_pairing,
    fderiv_selfMetricFlat_symm g x z v w]
  ring

lemma compact_selfMetricFlat_lower (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ selfMetricFlat g x v v :=
  compact_positive_bilinear_lower hK (selfMetricFlat g) (contDiff_selfMetricFlat g).continuous
    (fun x _ _ hv => selfMetricFlat_pos g x hv)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalJetMapFirstPhase
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_metric_orthonormal_frame (g : SmoothMetric E E) (p : E) :
    ∃ A : E ≃L[ℝ] E, ∀ v w, selfMetricFlat g p (A v) (A w) = inner ℝ v w := by
  let : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ,E) x) :=
    ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) p
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) p) :=
    Module.Finite.equiv j.symm.toLinearEquiv
  let e : E ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ,E) p :=
    (stdOrthonormalBasis ℝ E).equiv
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ,E) p))
      (finCongr j.toLinearEquiv.finrank_eq.symm)
  refine ⟨e.toContinuousLinearEquiv.trans j, ?_⟩
  intro v w
  have h := e.inner_map_map v w
  change g.inner p (e v) (e w) = inner ℝ v w at h
  simpa only [selfMetricFlat, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    j] using h

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_zero (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    normalJetMap p A C 0 = p := by simp [normalJetMap]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    HasFDerivAt (normalJetMap p A C) (A - C x) x := by
  have h := ((hasFDerivAt_const p x).add A.hasFDerivAt).sub
    ((C.hasFDerivAt.clm_apply (hasFDerivAt_id x)).const_smul (1/2 : ℝ))
  change HasFDerivAt (fun y => p + A y - (1/2 : ℝ) • C y y) (A - C x) x
  apply h.congr_fderiv
  ext v
  simp only [_root_.sub_apply, _root_.add_apply,
    zero_add, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, id_eq, hC v x, ← two_smul ℝ, smul_smul]
  norm_num

omit [FiniteDimensional ℝ E] in
lemma fderiv_normalJetMap (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (hC : ∀ v w, C v w = C w v) (x : E) :
    fderiv ℝ (normalJetMap p A C) x = A - C x :=
  (hasFDerivAt_normalJetMap p A C hC x).fderiv


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma normalJetMap_remainder (p : E) (A : E →L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    normalJetMap p A C x - normalJetMap p A C y - A (x-y) =
      -(1/2 : ℝ) • (C x (x-y) + C (x-y) y) := by
  simp only [normalJetMap, map_sub, _root_.sub_apply, smul_add, smul_sub]
  module

lemma normalJetMap_derivative_invertible (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) {x : E}
    (hx : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1) :
    (A.toContinuousLinearMap - C x).IsInvertible := by
  have hi : Function.Injective (A.toContinuousLinearMap - C x) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change A v - C x v = 0 at hv
    have he : A v = C x v := sub_eq_zero.mp hv
    have hh : ‖v‖ ≤ (‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖) * ‖v‖ := by
      calc
        ‖v‖ = ‖A.symm (A v)‖ := by rw [A.symm_apply_apply]
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A v‖ := (A.symm : E →L[ℝ] E).le_opNorm _
        _ = ‖(A.symm : E →L[ℝ] E)‖ * ‖C x v‖ := by rw [he]
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (‖C x‖ * ‖v‖) := by gcongr; exact (C x).le_opNorm _
        _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ((‖C‖ * ‖x‖) * ‖v‖) := by gcongr; exact C.le_opNorm _
        _ = _ := by ring
    have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hn
  let e := LinearEquiv.ofBijective (A.toContinuousLinearMap - C x).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_FrameDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma metricFrameSet_fiber_nonempty (g : SmoothMetric E E) {K : Set E} {p : E}
    (hp : p ∈ K) : ∃ A : E →L[ℝ] E, (p,A) ∈ metricFrameSet g K := by
  obtain ⟨A,hA⟩ := exists_metric_orthonormal_frame g p
  exact ⟨A, hp, hA⟩

local instance frameDualNorm_r8d926e_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.YauCounterexamples.frameDualSpace
local instance frameFormNorm_r8d926e_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace_r8d926e_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_isClosed (g : SmoothMetric E E) {K : Set E} (hK : IsClosed K) :
    IsClosed (metricFrameSet g K) := by
  apply (hK.preimage continuous_fst).inter
  change IsClosed {q : E × (E →L[ℝ] E) | ∀ v w : E,
    selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  exact isClosed_eq
    (((contDiff_selfMetricFlat g).continuous.comp continuous_fst).clm_apply
      (continuous_snd.clm_apply continuous_const) |>.clm_apply
      (continuous_snd.clm_apply continuous_const)) continuous_const

lemma metricFrameSet_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2‖ ≤ R := by
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_⟩
  intro q hq
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml q.1 hq.1 (q.2 v)
  rw [hq.2 v v, real_inner_self_eq_norm_sq] at hlow
  have hh : Real.sqrt m * ‖q.2 v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]

theorem metricFrameSet_isCompact (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    IsCompact (metricFrameSet g K) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  apply (hK.prod (isCompact_closedBall (0 : E →L[ℝ] E) R)).of_isClosed_subset
    (metricFrameSet_isClosed g hK.isClosed)
  intro q hq
  exact ⟨hq.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb q hq⟩

omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_injective (g : SmoothMetric E E) {K : Set E}
    {q : E × (E →L[ℝ] E)} (hq : q ∈ metricFrameSet g K) : Function.Injective q.2 := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change q.2 v = 0 at hv
  have h := hq.2 v v
  rw [hv, map_zero] at h
  exact inner_self_eq_zero.mp h.symm

lemma metricFrameSet_equiv (g : SmoothMetric E E) {K : Set E}
    {q : E × (E →L[ℝ] E)} (hq : q ∈ metricFrameSet g K) :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = q.2 := by
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective q.2.toLinearMap
    ((LinearMap.injective_iff_surjective).mp (metricFrameSet_injective g hq) |>
      fun hs => ⟨metricFrameSet_injective g hq,hs⟩)
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalFamilyVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyBiVecSpace
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFamilyDualSpace
local instance normalFamilyFormNorm_r8d926e_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance normalFamilyFormSpace_r8d926e_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma contDiff_frameChristoffel (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) =>
      (metricChristoffel g q.1).bilinearComp q.2 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : E × (E →L[ℝ] E) => (metricChristoffel g q.1).comp q.2) :=
    ((contDiff_metricChristoffel g).comp contDiff_fst).clm_comp contDiff_snd
  have h2 := (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h1
  have h3 := h2.clm_comp contDiff_snd
  exact (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap.contDiff.comp h3

lemma contDiff_normalJetFamily (g : SmoothMetric E E) :
    ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E =>
      normalJetMap q.1.1 q.1.2 ((metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) q.2) := by
  have hC : ContDiff ℝ ∞ (fun q : (E × (E →L[ℝ] E)) × E => (metricChristoffel g q.1.1).bilinearComp q.1.2 q.1.2) :=
    (contDiff_frameChristoffel g).comp contDiff_fst
  exact (contDiff_fst.fst.add (contDiff_fst.snd.clm_apply contDiff_snd)).sub
    ((hC.clm_apply contDiff_snd |>.clm_apply contDiff_snd).const_smul (1/2 : ℝ))

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma normal_iteratedFDeriv_comp_clm_at (L : F →L[ℝ] E) {f : E → G} {x : F} (n : ℕ)
    (hf : ContDiffAt ℝ n f (L x)) :
    iteratedFDeriv ℝ n (f ∘ L) x =
      (iteratedFDeriv ℝ n f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨U,hU,hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hVo,hx⟩ := mem_nhds_iff.mp hU
  have he := L.iteratedFDerivWithin_comp_right (hu.mono hVU) hVo.uniqueDiffOn
    (hVo.preimage L.continuous).uniqueDiffOn hx (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_of_isOpen n hVo hx,
    iteratedFDerivWithin_of_isOpen n (hVo.preimage L.continuous) hx] at he
  exact he

lemma parameter_iteratedFDeriv (f : P × E → F) (t : P) (x : E) (n : ℕ)
    (hf : ContDiffAt ℝ n f (t,x)) :
    iteratedFDeriv ℝ n (fun y => f (t,y)) x =
      (iteratedFDeriv ℝ n f (t,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let q : P × E → F := fun z => f ((t,0)+z)
  have hq : ContDiffAt ℝ n q (L x) := by
    have hg : ContDiffAt ℝ n (fun z : P × E => (t,0)+z) (L x) := by fun_prop
    exact (show ContDiffAt ℝ n f ((t,0)+L x) by simpa [L] using hf).comp (L x) hg
  have hj := normal_iteratedFDeriv_comp_clm_at L n hq
  simpa [q,L,Function.comp_def,iteratedFDeriv_comp_add_left] using hj

lemma continuousAt_parameter_iteratedFDeriv (f : P × E → F) {z : P × E} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f z) :
    ContinuousAt (fun w : P × E => iteratedFDeriv ℝ n (fun y => f (w.1,y)) w.2) z := by
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ P E)).continuousAt.comp
      (hf.continuousAt_iteratedFDeriv (k := n) (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).eventually (by simp)] with w hw
  exact parameter_iteratedFDeriv f w.1 w.2 n hw


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
section ParameterDerivative
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma continuous_parameter_iteratedFDeriv (f : P × E → F) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    Continuous (fun q : P × E => iteratedFDeriv ℝ k (fun x => f (q.1,x)) q.2) :=
  continuous_iff_continuousAt.mpr (fun _ => continuousAt_parameter_iteratedFDeriv f k hf.contDiffAt)
end ParameterDerivative

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalInverseVecNorm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_open_inverse {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ (∞ : WithTop ℕ∞) f s) (hinj : InjOn f s)
    (hd : ∀ x ∈ s, (fderiv ℝ f x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ e.source = s ∧
      ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target := by
  have hop : ∀ t : Set E, IsOpen t → t ⊆ s → IsOpen (f '' t) := by
    intro t ht hts
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨D,hD⟩ := hd x (hts hx)
    have hfc : ContDiffAt ℝ (∞ : WithTop ℕ∞) f x := (hf x (hts hx)).contDiffAt (hs.mem_nhds (hts hx))
    have hfd : HasFDerivAt f (D : E →L[ℝ] F) x := by
      rw [hD]
      exact (hfc.differentiableAt (by simp)).hasFDerivAt
    let e := hfc.toOpenPartialHomeomorph f hfd (by simp)
    have hxe : x ∈ e.source := hfc.mem_toOpenPartialHomeomorph_source hfd (by simp)
    have hmem : f x ∈ e '' (e.source ∩ t) := ⟨x,⟨hxe,hx⟩,rfl⟩
    apply Filter.mem_of_superset ((e.isOpen_image_source_inter ht).mem_nhds hmem)
    rintro _ ⟨y,hy,rfl⟩
    exact ⟨y,hy.2,rfl⟩
  let p := hinj.toPartialEquiv f s
  have ho : IsOpenMap (s.domRestrict f) := by
    intro t ht
    have hv : IsOpen (Subtype.val '' t : Set E) := hs.isOpenMap_subtype_val t ht
    have hz := hop (Subtype.val '' t) hv (by rintro _ ⟨a,ha,rfl⟩; exact a.property)
    change IsOpen ((fun x : s => f x) '' t)
    simpa only [Set.image_image] using hz
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn ho hs
  refine ⟨e,rfl,rfl,?_⟩
  intro y hy
  obtain ⟨D,hD⟩ := hd (e.symm y) (e.map_target hy)
  have hfc : ContDiffAt ℝ (∞ : WithTop ℕ∞) f (e.symm y) :=
    (hf _ (e.map_target hy)).contDiffAt (hs.mem_nhds (e.map_target hy))
  have hfd : HasFDerivAt f (D : E →L[ℝ] F) (e.symm y) := by
    rw [hD]
    exact (hfc.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hy hfd hfc).contDiffWithinAt
end

section
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma familyTotal_derivative_invertible {f : P × E → E} {q : P} {x : E}
    (hf : DifferentiableAt ℝ f (q,x))
    (hd : (fderiv ℝ (fun y => f (q,y)) x).IsInvertible) :
    (fderiv ℝ (fun a : P × E => (a.1,f a)) (q,x)).IsInvertible := by
  let L := fderiv ℝ f (q,x)
  obtain ⟨D,hD⟩ := hd
  let A : P →L[ℝ] E := L.comp (ContinuousLinearMap.inl ℝ P E)
  let T := (ContinuousLinearEquiv.refl ℝ P).skewProd D A
  have hR : L.comp (ContinuousLinearMap.inr ℝ P E) = D := by
    have h := hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right q x)
    exact h.fderiv.symm.trans hD.symm
  have hL : (ContinuousLinearMap.fst ℝ P E).prod L = T.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    apply Prod.ext
    · rfl
    · change L a = D a.2 + L (a.1,0)
      have ha : a = (0,a.2) + (a.1,0) := by ext <;> simp
      calc
        L a = L (0,a.2) + L (a.1,0) := by conv_lhs => rw [ha]; rw [L.map_add]
        _ = D a.2 + L (a.1,0) := congrArg (fun v => v + L (a.1,0))
          (congrArg (fun M : E →L[ℝ] E => M a.2) hR)
  refine ⟨T,?_⟩
  exact ((hasFDerivAt_fst.prodMk hf.hasFDerivAt).fderiv.trans hL).symm
end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma isOpen_continuousLinearMap_isInvertible :
    IsOpen {A : E →L[ℝ] E | A.IsInvertible} := by
  have he : {A : E →L[ℝ] E | A.IsInvertible} = {A : E →L[ℝ] E | IsUnit A} := by
    ext A
    constructor
    · rintro ⟨e,rfl⟩
      exact e.toUnit.isUnit
    · rintro ⟨u,rfl⟩
      exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E u,rfl⟩
  rw [he]
  exact Units.isOpen

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.normalInverseVecNorm
attribute [local instance] OAI.YauCounterexamples.normalInverseVecSpace
local instance normalInverseBiVecNorm_r8d926e_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance normalInverseBiVecSpace_r8d926e_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma normalJetMap_injOn_small (p : E) (A : E ≃L[ℝ] E)
    (C : E →L[ℝ] E →L[ℝ] E) :
    InjOn (normalJetMap p A C)
      {x | ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1/2} := by
  intro x hx y hy he
  change ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖x‖ < 1/2 at hx
  change ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖y‖ < 1/2 at hy
  have hr := normalJetMap_remainder p A C x y
  rw [he,sub_self,zero_sub] at hr
  have hAv : A (x-y) = (1/2 : ℝ) • (C x (x-y) + C (x-y) y) := by
    calc
      _ = -(-(A (x-y))) := (neg_neg _).symm
      _ = _ := by
        change -(-((A : E →L[ℝ] E) (x-y))) = _
        rw [hr]; module
  have hB : ‖x-y‖ ≤
      ((‖(A.symm : E →L[ℝ] E)‖*‖C‖*‖x‖ +
        ‖(A.symm : E →L[ℝ] E)‖*‖C‖*‖y‖)/2) * ‖x-y‖ := by
    calc
      ‖x-y‖ = ‖A.symm (A (x-y))‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A (x-y)‖ := (A.symm : E →L[ℝ] E).le_opNorm _
      _ = ‖(A.symm : E →L[ℝ] E)‖ * ((1/2 : ℝ)*‖C x (x-y)+C (x-y) y‖) := by
        rw [hAv,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ((1/2 : ℝ)*
          ((‖C‖*‖x‖)*‖x-y‖ + (‖C‖*‖x-y‖)*‖y‖)) := by
        gcongr
        calc
          _ ≤ ‖C x (x-y)‖ + ‖C (x-y) y‖ := norm_add_le _ _
          _ ≤ _ := add_le_add ((C x).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)))
            ((C (x-y)).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right (C.le_opNorm _) (norm_nonneg _)))
      _ = _ := by ring
  have hn : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

lemma isOpen_normalFamilySource (g : SmoothMetric E E) : IsOpen (normalFamilySource g) := by
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  have hI := (isOpen_continuousLinearMap_isInvertible.preimage
    (continuous_snd.comp continuous_fst)).mem_nhds hw.1
  have hi : ContinuousAt (fun w : (E × (E →L[ℝ] E)) × E => w.1.2.inverse) w :=
    (hw.1.contDiffAt_map_inverse (n := (∞ : WithTop ℕ∞))).continuousAt.comp
      (f := fun w : (E × (E →L[ℝ] E)) × E => w.1.2)
      (continuous_snd.comp continuous_fst).continuousAt
  have hC : ContinuousAt (fun w : (E × (E →L[ℝ] E)) × E =>
      (metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) w :=
    ((contDiff_frameChristoffel g).comp contDiff_fst).continuous.continuousAt
  have hcn : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E =>
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖) w := by
    exact hC.norm
  have hm : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E => ‖z.1.2.inverse‖ *
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖) w := by
    exact hi.norm.mul hcn
  have hf : ContinuousAt (fun z : (E × (E →L[ℝ] E)) × E => ‖z.1.2.inverse‖ *
      ‖(metricChristoffel g z.1.1).bilinearComp z.1.2 z.1.2‖ * ‖z.2‖) w := by
    exact hm.mul continuous_snd.continuousAt.norm
  have hh := hf.eventually (gt_mem_nhds hw.2)
  exact inter_mem hI hh

lemma normalFamilyTotal_injOn (g : SmoothMetric E E) :
    InjOn (normalFamilyTotal g) (normalFamilySource g) := by
  rintro ⟨q,x⟩ hx ⟨q',y⟩ hy he
  have hq : q = q' := congrArg Prod.fst he
  subst q'
  refine Prod.ext (by rfl) ?_
  obtain ⟨A,hA⟩ := hx.1
  have hi : (A.symm : E →L[ℝ] E) = q.2.inverse := by
    rw [←hA,ContinuousLinearMap.inverse_equiv]
  have hh := normalJetMap_injOn_small q.1 A
    ((metricChristoffel g q.1).bilinearComp q.2 q.2)
  apply hh
  · simpa only [mem_ofPred_eq,hi] using hx.2
  · simpa only [mem_ofPred_eq,hi] using hy.2
  · simpa only [normalFamilyTotal,hA] using congrArg Prod.snd he

lemma normalFamilyTotal_smooth (g : SmoothMetric E E) : ContDiff ℝ (∞ : WithTop ℕ∞) (normalFamilyTotal g) :=
  contDiff_fst.prodMk (contDiff_normalJetFamily g)

lemma normalFamilyTotal_derivative_invertible (g : SmoothMetric E E)
    {w : (E × (E →L[ℝ] E)) × E} (hw : w ∈ normalFamilySource g) :
    (fderiv ℝ (normalFamilyTotal g) w).IsInvertible := by
  obtain ⟨A,hA⟩ := hw.1
  let C := (metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2
  have hi : (A.symm : E →L[ℝ] E) = w.1.2.inverse := by
    rw [←hA,ContinuousLinearMap.inverse_equiv]
  have hs : ‖(A.symm : E →L[ℝ] E)‖ * ‖C‖ * ‖w.2‖ < 1 := by
    rw [hi]
    exact hw.2.trans (by norm_num)
  have hCs : ∀ v z, C v z = C z v := by
    intro v z
    exact metricChristoffel_symm g w.1.1 (w.1.2 v) (w.1.2 z)
  have hd : (fderiv ℝ (normalJetMap w.1.1 w.1.2 C) w.2).IsInvertible := by
    rw [fderiv_normalJetMap w.1.1 w.1.2 C hCs]
    have h := normalJetMap_derivative_invertible A C hs
    simpa only [hA] using h
  exact familyTotal_derivative_invertible (f := fun a : (E × (E →L[ℝ] E)) × E =>
    normalJetMap a.1.1 a.1.2 ((metricChristoffel g a.1.1).bilinearComp a.1.2 a.1.2) a.2)
    ((contDiff_normalJetFamily g).differentiable (by simp) w) hd

theorem exists_normal_family_inverse (g : SmoothMetric E E) :
    ∃ e : OpenPartialHomeomorph ((E × (E →L[ℝ] E)) × E) ((E × (E →L[ℝ] E)) × E),
      (e : ((E × (E →L[ℝ] E)) × E) → ((E × (E →L[ℝ] E)) × E)) = normalFamilyTotal g ∧
      e.source = normalFamilySource g ∧ ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target :=
  smooth_open_inverse (isOpen_normalFamilySource g) (normalFamilyTotal_smooth g).contDiffOn
    (normalFamilyTotal_injOn g) (fun _ h => normalFamilyTotal_derivative_invertible g h)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_CompactThreePolynomialNet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
namespace YauCounterexamples

theorem compact_three_polynomial_net {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∀ n : ℝ, 1 ≤ n → ∃ t : Finset (Fin 3 → ℝ),
      (↑t : Set (Fin 3 → ℝ)) ⊆ K ∧ (t.card : ℝ) ≤ C*n^3 ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ c/n := by
  obtain ⟨B₀,hB₀⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  let B := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : ∀ x ∈ K, ‖x‖ ≤ B := fun x hx => (hB₀ x hx).trans (le_max_right _ _)
  let A := 4*B/c+3
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^3,pow_pos hA _,?_⟩
  intro n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let δ := c/(2*n)
  have hδ : 0 < δ := div_pos hc (mul_pos (by norm_num) hn0)
  let m := ⌈B/δ⌉₊
  have hm : B ≤ (m : ℝ)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (B/δ))
  obtain ⟨t,htK,htcard,htcover⟩ := cube_subset_finite_net 3 m δ hδ K
    (fun x hx => (hbound x hx).trans hm)
  refine ⟨t,htK,?_,?_⟩
  · have hm' : (m : ℝ) < B/δ+1 := Nat.ceil_lt_add_one (div_nonneg hB.le hδ.le)
    have heq : B/δ = (2*B/c)*n := by dsimp [δ]; field_simp
    have hbase : (2*m+1 : ℝ) ≤ A*n := by
      dsimp [A]
      rw [heq] at hm'
      have hid : (4*B/c+3)*n = 2*((2*B/c)*n)+3*n := by ring
      rw [hid]
      linarith
    calc
      (t.card : ℝ) ≤ ((2*m+1)^3 : ℕ) := by exact_mod_cast htcard
      _ = (2*(m : ℝ)+1)^3 := by norm_cast
      _ ≤ (A*n)^3 := pow_le_pow_left₀ (by positivity) hbase _
      _ = A^3*n^3 := mul_pow _ _ _
  · intro x hx
    obtain ⟨y,hy,hd⟩ := htcover x hx
    refine ⟨y,hy,?_⟩
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [δ]
    field_simp

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_MetricCenterPolynomialNetCoverage
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.coordinateRegionMeasure_finite _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter
open scoped Topology ContDiff

theorem normalCoordinateMap_inverse_bound
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∃ C ≥ 1, ∀ q ∈ metricFrameSet g K,
      ∀ v : Fin 3 → ℝ, ‖v‖ ≤ r → ∃ x : Fin 3 → ℝ,
        normalCoordinateMap g q x = normalWaveEquiv.symm q.1+v ∧ ‖x‖ ≤ C*‖v‖ := by
  obtain ⟨e,he,hs,hi⟩ := exists_normal_family_inverse g
  let R : NormalWaveParameter × (Fin 3 → ℝ) → NormalWaveParameter × NormalWaveSpace :=
    fun w => (w.1,w.1.1+normalWaveEquiv w.2)
  have hR : ContDiff ℝ ∞ R := contDiff_fst.prodMk
    ((contDiff_fst.comp contDiff_fst).add (normalWaveEquiv.contDiff.comp contDiff_snd))
  have h0 (q : NormalWaveParameter) (hq : q ∈ metricFrameSet g K) : (q,0) ∈ e.source := by
    rw [hs]
    exact ⟨metricFrameSet_equiv g hq,by simp⟩
  have he0 (q : NormalWaveParameter) : e (q,0) = R (q,0) := by
    rw [he]
    simp [normalFamilyTotal,R,normalJetMap_zero]
  have hsub : metricFrameSet g K ×ˢ {(0 : Fin 3 → ℝ)} ⊆ R ⁻¹' e.target := by
    rintro ⟨q,v⟩ ⟨hq,hv⟩
    have hv0 : v = 0 := hv
    subst v
    change R (q,0) ∈ e.target
    rw [←he0 q]
    exact e.map_source (h0 q hq)
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton (e.open_target.preimage hR.continuous) hsub
  obtain ⟨r₁,hr₁,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  let r := r₁/2
  have hr : 0 < r := half_pos hr₁
  let L := metricFrameSet g K ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) r
  have hL : IsCompact L := (metricFrameSet_isCompact g hK).prod (isCompact_closedBall 0 r)
  have hLt : R '' L ⊆ e.target := by
    rintro _ ⟨⟨q,v⟩,⟨hq,hv⟩,rfl⟩
    exact hUV ⟨hKU hq,hrV ((Metric.closedBall_subset_ball (half_lt_self hr₁)) hv)⟩
  obtain ⟨ψ,hψ,hEq⟩ := smooth_extension_near_compact (hL.image hR.continuous)
    e.open_target hLt hi.snd
  let f : NormalWaveParameter × (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
    fun w => normalWaveEquiv.symm (ψ (R w))
  have hf : ContDiff ℝ ∞ f := normalWaveEquiv.symm.contDiff.comp (hψ.comp hR)
  have hfEq (w : NormalWaveParameter × (Fin 3 → ℝ)) (hw : w ∈ L) :
      f w = normalWaveEquiv.symm (e.symm (R w)).2 := by
    change normalWaveEquiv.symm (ψ (R w)) = _
    congr 1
    exact ((hEq.filter_mono (nhds_le_nhdsSet (mem_image_of_mem R hw))).self_of_nhds).symm
  have hf0 (q : NormalWaveParameter) (hq : q ∈ metricFrameSet g K) : f (q,0) = 0 := by
    rw [hfEq (q,0) ⟨hq,Metric.mem_closedBall_self hr.le⟩,←he0 q,e.left_inv (h0 q hq)]
    exact map_zero _
  obtain ⟨C₀,hC₀⟩ := hL.exists_bound_of_continuousOn
    ((continuous_parameter_iteratedFDeriv f hf 1).continuousOn)
  let C := max 1 C₀
  refine ⟨r,hr,C,le_max_left _ _,?_⟩
  intro q hq v hv
  have hvmem : v ∈ Metric.closedBall (0 : Fin 3 → ℝ) r := by
    simpa [Metric.mem_closedBall,dist_zero_right] using hv
  refine ⟨f (q,v),?_,?_⟩
  · have htarget : R (q,v) ∈ e.target := hLt (mem_image_of_mem R ⟨hq,hvmem⟩)
    have hright := e.right_inv htarget
    have hfst : (e.symm (R (q,v))).1 = q := by
      have hh := congrArg Prod.fst hright
      simpa only [he,normalFamilyTotal,R] using hh
    have hsnd := congrArg Prod.snd hright
    rw [he] at hsnd
    change normalJetMap (e.symm (R (q,v))).1.1 (e.symm (R (q,v))).1.2
      ((metricChristoffel g (e.symm (R (q,v))).1.1).bilinearComp
        (e.symm (R (q,v))).1.2 (e.symm (R (q,v))).1.2) (e.symm (R (q,v))).2 =
      q.1+normalWaveEquiv v at hsnd
    rw [hfst] at hsnd
    rw [hfEq (q,v) ⟨hq,hvmem⟩]
    simpa only [normalCoordinateMap,ContinuousLinearEquiv.apply_symm_apply,map_add,
      ContinuousLinearEquiv.symm_apply_apply] using congrArg normalWaveEquiv.symm hsnd
  · have hm := (convex_closedBall (0 : Fin 3 → ℝ) r).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z)
      (fun z hz => by
        have hb := hC₀ (q,z) ⟨hq,hz⟩
        rw [norm_iteratedFDeriv_one] at hb
        exact hb.trans (le_max_right 1 C₀))
      (Metric.mem_closedBall_self hr.le) hvmem
    simpa only [Function.comp_apply,id_eq,hf0 q hq,sub_zero] using hm


end

open Set
open scoped Topology ContDiff
theorem metric_center_polynomial_net_with_coverage_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ Q > 0, ∀ n : ℝ, 1 ≤ n →
      ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
        (t.card : ℝ) ≤ Q*n^3 ∧
        ∀ y ∈ normalWaveEquiv.symm '' K, ∃ i : t, ∃ x : Fin 3 → ℝ,
          ‖x‖ < r₀ ∧ ‖x‖ ≤ 1/n ∧ normalCoordinateMap g (p i) x = y ∧
          n*‖normalWaveEquiv y-(p i).1.1‖ ≤ 1 := by
  classical
  obtain ⟨ρ,hρ,A,hA,hInv⟩ := normalCoordinateMap_inverse_bound g hK
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let B := ‖normalWaveEquiv.toContinuousLinearMap‖+1
  have hB : 0 < B := by dsimp [B]; positivity
  let c := min (min ρ (min (r₀/(2*A)) (1/A))) (1/B)
  have hc : 0 < c := lt_min (lt_min hρ (lt_min (div_pos hr₀ (by positivity)) (div_pos zero_lt_one hA0))) (div_pos zero_lt_one hB)
  obtain ⟨Q,hQ,hnet⟩ := compact_three_polynomial_net
    (hK.image normalWaveEquiv.symm.continuous) c hc
  refine ⟨Q,hQ,?_⟩
  intro n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨t,ht,htcard,htcover⟩ := hnet n hn
  have hcenter (i : t) : normalWaveEquiv i.1 ∈ K := by
    obtain ⟨z,hz,hzi⟩ := ht i.property
    rw [←hzi,ContinuousLinearEquiv.apply_symm_apply]
    exact hz
  choose F hF using (fun i : t => metricFrameSet_fiber_nonempty g (hcenter i))
  let p : t → metricFrameSet g K := fun i => ⟨(normalWaveEquiv i.1,F i),hF i⟩
  refine ⟨t,p,htcard,?_⟩
  intro y hy
  obtain ⟨z,hz,hd⟩ := htcover y hy
  let i : t := ⟨z,hz⟩
  let v := y-z
  have hv : ‖v‖ ≤ c/n := by simpa [v,dist_eq_norm] using hd
  have hcn : c/n ≤ c := div_le_self hc.le hn
  have hvρ : ‖v‖ ≤ ρ := hv.trans (hcn.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨x,hx,hxb⟩ := hInv (p i) (p i).property v hvρ
  refine ⟨i,x,?_,?_,?_,?_⟩
  · have hb : A*c ≤ r₀/2 := by
      have hc' : c ≤ r₀/(2*A) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have h' := (le_div_iff₀ (show 0 < 2*A by positivity)).mp hc'
      nlinarith
    calc
      ‖x‖ ≤ A*‖v‖ := hxb
      _ ≤ A*c := mul_le_mul_of_nonneg_left (hv.trans hcn) hA0.le
      _ ≤ r₀/2 := hb
      _ < r₀ := half_lt_self hr₀
  · have hb : A*c ≤ 1 := by
      have hc' : c ≤ 1/A := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [(le_div_iff₀ hA0).mp hc']
    calc
      ‖x‖ ≤ A*‖v‖ := hxb
      _ ≤ A*(c/n) := mul_le_mul_of_nonneg_left hv hA0.le
      _ = (A*c)/n := by ring
      _ ≤ 1/n := div_le_div_of_nonneg_right hb hn0.le
  · have heq : normalWaveEquiv.symm (p i).1.1 = z := normalWaveEquiv.symm_apply_apply z
    rw [heq] at hx
    simpa only [v,add_sub_cancel] using hx

  · have hBc : B*c ≤ 1 := by
      have hh : c ≤ 1/B := min_le_right _ _
      have hh' := (le_div_iff₀ hB).mp hh
      nlinarith
    have hdist : ‖normalWaveEquiv y-(p i).1.1‖ ≤ B*(c/n) := by
      change ‖normalWaveEquiv y-normalWaveEquiv z‖ ≤ _
      rw [←map_sub]
      calc
        _ ≤ ‖normalWaveEquiv.toContinuousLinearMap‖*‖v‖ := normalWaveEquiv.toContinuousLinearMap.le_opNorm v
        _ ≤ B*‖v‖ := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg _)
        _ ≤ B*(c/n) := mul_le_mul_of_nonneg_left hv hB.le
    calc
      _ ≤ n*(B*(c/n)) := mul_le_mul_of_nonneg_left hdist hn0.le
      _ = B*c := by field_simp
      _ ≤ 1 := hBc


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage_oai := @OAI.YauCounterexamples.metric_center_polynomial_net_with_coverage_oai
