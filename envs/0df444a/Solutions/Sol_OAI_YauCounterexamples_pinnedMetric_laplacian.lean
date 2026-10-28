-- Prove2me | solution 1 for OAI.YauCounterexamples.pinnedMetric_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:39:52.574229+00:00
-- url     : https://prove2.me/submissions/8a36a5e2-09e6-4b51-b97c-36ed679680c1

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A007

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ClmMatrixAlgHom
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma hasDerivAt_det_exp_smul (K : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • K)).det)
      ((NormedSpace.exp (t • K)).det * K.trace) t := by
  have hu : IsUnit (NormedSpace.exp (t • K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (NormedSpace.isUnit_exp (t • K))
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) K t
  have hd := (differentiable_det (NormedSpace.exp (t • K))).hasFDerivAt.comp_hasDerivAt t he
  erw [fderiv_det_apply _ _ hu,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at hd
  exact hd

theorem matrix_det_exp (K : Matrix ι ι ℝ) :
    (NormedSpace.exp K).det = Real.exp K.trace := by
  let f : ℝ → ℝ := fun t => (NormedSpace.exp (t • K)).det * Real.exp (-t * K.trace)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have hh := (hasDerivAt_det_exp_smul K t).mul
      (((hasDerivAt_id t).neg.mul_const K.trace).exp)
    convert hh using 1 <;> first | rfl | ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
    (fun t => (hf t).deriv) 1 0
  have hfe : (NormedSpace.exp K).det * Real.exp (-K.trace) = 1 := by
    simpa only [f,one_smul,neg_mul,one_mul,zero_smul,NormedSpace.exp_zero,Matrix.det_one,
      neg_zero,zero_mul,Real.exp_zero,mul_one] using hc
  calc (NormedSpace.exp K).det =
      (NormedSpace.exp K).det * (Real.exp (-K.trace) * Real.exp K.trace) := by
        rw [← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _ = Real.exp K.trace := by rw [← mul_assoc,hfe,one_mul]

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open scoped Matrix.Norms.Operator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma clmMatrix_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap =
      NormedSpace.exp (LinearMap.toMatrix b b K.toLinearMap) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact NormedSpace.map_exp (clmMatrixAlgHom b)
    (clmMatrixAlgHom b).toLinearMap.continuous_of_finiteDimensional K

lemma clm_det_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.det (NormedSpace.exp K).toLinearMap =
      Real.exp (LinearMap.trace ℝ E K.toLinearMap) := by
  rw [← LinearMap.det_toMatrix b,clmMatrix_exp b K,matrix_det_exp,
    LinearMap.trace_eq_matrix_trace ℝ b]

omit [FiniteDimensional ℝ E] in
lemma matrixOfForm_pullback (b : Module.Basis ι ℝ E) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E) :
    matrixOfForm b ((D.precomp ℝ).comp (G.comp D)) =
      (clmMatrixAlgHom b D).transpose * matrixOfForm b G * clmMatrixAlgHom b D := by
  ext i j
  change G (D (b i)) (D (b j)) =
    ((LinearMap.toMatrix b b D.toLinearMap).transpose * matrixOfForm b G *
      LinearMap.toMatrix b b D.toLinearMap) i j
  conv_lhs => arg 1; rw [← b.sum_repr (D (b i))]
  conv_lhs => arg 2; rw [← b.sum_repr (D (b j))]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,matrixOfForm,
    LinearMap.toMatrix_apply,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (b.repr (D (b j))) k * ((b.repr (D (b i))) l * G (b l) (b k)) =
    (b.repr (D (b i))) l * G (b l) (b k) * (b.repr (D (b j))) k
  ring

theorem tracefree_exp_preserves_gram_det (b : Module.Basis ι ℝ E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (htr : LinearMap.trace ℝ E K.toLinearMap = 0) :
    (matrixOfForm b (((NormedSpace.exp K).precomp ℝ).comp
      (G.comp (NormedSpace.exp K)))).det = (matrixOfForm b G).det := by
  rw [matrixOfForm_pullback,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hd : (clmMatrixAlgHom b (NormedSpace.exp K)).det = 1 := by
    change (LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap).det = 1
    rw [LinearMap.det_toMatrix,clm_det_exp b K,htr,Real.exp_zero]
  rw [hd,one_mul,mul_one]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_DerivExpSmulZero
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma clm_exp_fix_kernel {K : E →L[ℝ] E} {v : E} (h : K v = 0) :
    (NormedSpace.exp K) v = v := by
  have hp : ∀ n : ℕ, (K^(n+1)) v = 0 := by
    intro n
    rw [pow_succ,mul_apply_eq_comp,h,map_zero]
  have he := (NormedSpace.expSeries_summable' (𝕂 := ℝ) K).hasSum.map
    (ContinuousLinearMap.apply ℝ E v).toAddMonoidHom
    (ContinuousLinearMap.apply ℝ E v).continuous
  have hs : HasSum (fun n : ℕ => (n.factorial:ℝ)⁻¹ • ((K^n) v)) v := by
    convert (hasSum_ite_eq (0:ℕ) v) using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    cases n with
    | zero => simp
    | succ n => simp [hp n]
  have hx : HasSum (fun n : ℕ => (n.factorial:ℝ)⁻¹ • ((K^n) v))
      ((NormedSpace.exp K) v) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    change HasSum (fun n : ℕ => ((n.factorial:ℝ)⁻¹ • (K^n)) v)
      ((∑' n : ℕ, (n.factorial:ℝ)⁻¹ • (K^n)) v) at he
    simpa only [smul_apply] using he
  exact hx.unique hs
lemma clm_exp_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (hK : ∀ v w, G (K v) w = G v (K w)) (v w : E) :
    G ((NormedSpace.exp K) v) w = G v ((NormedSpace.exp K) w) := by
  have hp (n : ℕ) : ∀ v w, G ((K^n) v) w = G v ((K^n) w) := by
    induction n with
    | zero => intro v w; simp
    | succ n ih =>
      intro v w
      calc G ((K^(n+1)) v) w = G (K ((K^n) v)) w := by rw [pow_succ',mul_apply_eq_comp]
        _ = G ((K^n) v) (K w) := hK _ _
        _ = G v ((K^n) (K w)) := ih _ _
        _ = G v ((K^(n+1)) w) := by rw [pow_succ,mul_apply_eq_comp]
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (G.flip w).comp (ContinuousLinearMap.apply ℝ E v) -
      (G v).comp (ContinuousLinearMap.apply ℝ E w)
  have hL (n : ℕ) : L (K^n) = 0 := sub_eq_zero.mpr (hp n v w)
  have he : L (NormedSpace.exp K) = 0 := by
    rw [NormedSpace.exp_eq_tsum ℝ,L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) K)]
    simp only [map_smul,hL,smul_zero,tsum_zero]
  exact sub_eq_zero.mp he

lemma pinned_exp_pairing (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (hK : ∀ v w, G (K v) w = G v (K w)) {v : E} (hv : K v = 0) (w : E) :
    G ((NormedSpace.exp K) v) ((NormedSpace.exp K) w) = G v w := by
  rw [clm_exp_fix_kernel hv,← clm_exp_selfAdjoint G K hK v w,clm_exp_fix_kernel hv]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_inner (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w =
      g.inner x ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) v)
        ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) w) := rfl

lemma pinnedMetric_preserves_gradient_pairing (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ) (x : M)
    (hsa : ∀ v w, g.inner x (K x v) w = g.inner x v (K x w))
    {v : TangentSpace 𝓘(ℝ,E) x} (hv : K x v = 0) (w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w = g.inner x v w := by
  rw [pinnedMetric_inner]
  apply pinned_exp_pairing (E := E)
  · intro a b
    change g.inner x ((-t/2) • K x a) b = g.inner x a ((-t/2) • K x b)
    erw [map_smul, smul_apply, map_smul]
    exact congrArg (fun r : ℝ => (-t/2) • r) (hsa a b)
  · change (-t/2) • K x v = 0
    rw [hv,smul_zero]


end


section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_det (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients (pinnedMetric g K hK t) p y).det =
      (metricCoefficients g p y).det := by
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E p).symm y)
  let A : E →L[ℝ] E := K ((chartAt E p).symm y)
  have ht : LinearMap.trace ℝ E (((-t/2) • A).toLinearMap) = 0 := by
    change LinearMap.trace ℝ E ((-t/2) • A.toLinearMap) = 0
    rw [map_smul,htr,smul_zero]
  exact tracefree_exp_preserves_gram_det (chartTangentBasis p y hy) G ((-t/2) • A) ht


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff Matrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma metricGradient_coordinate_pairing (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    g.inner ((chartAt E p).symm y) (metricGradient g u ((chartAt E p).symm y))
      (coordinateVector p y i) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) := by
  rw [metricGradient_pairing]
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.chart_mem_maximalAtlas p) hy).mdifferentiableAt (by simp)
  have hh := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at hh
  rw [hh]
  rfl

lemma metricGradient_coordinates (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) =
      (chartTangentBasis p y hy).equivFun
        (show E from metricGradient g u ((chartAt E p).symm y)) := by
  let b := chartTangentBasis p y hy
  let v : E := metricGradient g u ((chartAt E p).symm y)
  have he : (metricCoefficients g p y) *ᵥ (b.equivFun v) =
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) := by
    ext i
    rw [← metricGradient_coordinate_pairing g hu p y hy i]
    change (∑ j, g.inner ((chartAt E p).symm y) (b i) (b j) * b.equivFun v j) =
      g.inner ((chartAt E p).symm y) v (b i)
    rw [g.symm _ v (b i)]
    conv_rhs => arg 2; rw [← b.sum_repr v]
    have hsum (L : E →L[ℝ] ℝ) :
        (∑ j, L (b j) * b.repr v j) = L (∑ j, b.repr v j • b j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact hsum (g.inner ((chartAt E p).symm y) (b i))
  rw [← he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne'),Matrix.one_mulVec]

lemma pinnedMetric_gradient (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (u : M → ℝ) (hker : ∀ x, K x (metricGradient g u x) = 0) (t : ℝ) (x : M) :
    metricGradient (pinnedMetric g K hK t) u x = metricGradient g u x := by
  symm
  apply metricGradient_unique
  intro w
  rw [pinnedMetric_preserves_gradient_pairing g K hK t x (hsa x) (hker x) w,
    metricGradient_pairing]

lemma pinnedMetric_flux (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hker : ∀ x, K x (metricGradient g u x) = 0)
    (t : ℝ) (p : M) (y : E) (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    metricFlux (pinnedMetric g K hK t) u p y i = metricFlux g u p y i := by
  have he : (metricCoefficients (pinnedMetric g K hK t) p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) =
      (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) := by
    rw [metricGradient_coordinates _ hu p y hy,metricGradient_coordinates _ hu p y hy,
      pinnedMetric_gradient g K hK hsa u hker t]
  unfold metricFlux
  rw [pinnedMetric_det g K hK htr t p y hy]
  exact congrArg (fun v : CoordIndex E → ℝ => Real.sqrt (metricCoefficients g p y).det * v i) he

theorem pinnedMetric_laplacian_oai (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hker : ∀ x, K x (metricGradient g u x) = 0) (t : ℝ) (x : M) :
    laplaceBeltrami (pinnedMetric g K hK t) u x = laplaceBeltrami g u x := by
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  change (Real.sqrt (metricCoefficients (pinnedMetric g K hK t) x ((chartAt E x) x)).det)⁻¹ *
      (∑ i, fderiv ℝ (fun y => metricFlux (pinnedMetric g K hK t) u x y i)
        ((chartAt E x) x) (Module.finBasis ℝ E i)) =
    (Real.sqrt (metricCoefficients g x ((chartAt E x) x)).det)⁻¹ *
      (∑ i, fderiv ℝ (fun y => metricFlux g u x y i)
        ((chartAt E x) x) (Module.finBasis ℝ E i))
  rw [pinnedMetric_det g K hK htr t x ((chartAt E x) x) hx]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => metricFlux (pinnedMetric g K hK t) u x y i) =ᶠ[𝓝 ((chartAt E x) x)]
      (fun y => metricFlux g u x y i) := by
    filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
    exact pinnedMetric_flux g K hK hsa htr hu hker t x y hy i
  rw [he.fderiv_eq]


end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.pinnedMetric_laplacian_oai.{u_1, u_2} := @OAI.YauCounterexamples.pinnedMetric_laplacian_oai.{u_1, u_2}
