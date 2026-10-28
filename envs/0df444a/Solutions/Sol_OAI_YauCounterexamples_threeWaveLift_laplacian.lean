-- Prove2me | solution 1 for OAI.YauCounterexamples.threeWaveLift_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:32:48.536556+00:00
-- url     : https://prove2.me/submissions/e0feb871-594b-4069-b02f-746bc42de680

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_MixedJacobianMatrix
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
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma mixed_jacobianMatrix_apply (b c : Module.Basis ι ℝ E) (f : E → E) (x : E) (i j : ι) :
    mixed_jacobianMatrix b c f x i j = c.coord i (fderiv ℝ f x (b j)) := by
  simp only [mixed_jacobianMatrix, LinearMap.toMatrix_apply, Module.Basis.coord_apply,
    ContinuousLinearMap.coe_coe]

lemma mixed_differentiableAt_jacobian {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (b c : Module.Basis ι ℝ E) :
    DifferentiableAt ℝ (mixed_jacobianMatrix b c f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  let L : E →L[ℝ] ℝ := (c.coord i).toContinuousLinearMap
  simp only [mixed_jacobianMatrix_apply]
  change DifferentiableAt ℝ (fun y => L (fderiv ℝ f y (b j))) x
  exact L.differentiableAt.comp x (hd.clm_apply (differentiableAt_const _))

lemma mixed_fderiv_jacobian_apply {f : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (b c : Module.Basis ι ℝ E) (v : E) (i j : ι) :
    fderiv ℝ (mixed_jacobianMatrix b c f) x v i j =
      c.coord i (fderiv ℝ (fderiv ℝ f) x v (b j)) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_matrix_apply (mixed_differentiableAt_jacobian hf b c)]
  let L : E →L[ℝ] ℝ := (c.coord i).toContinuousLinearMap
  simp only [mixed_jacobianMatrix_apply]
  change fderiv ℝ (fun y => L (fderiv ℝ f y (b j))) x v = _
  rw [show (fun y => L (fderiv ℝ f y (b j))) =
      L ∘ (fun y => fderiv ℝ f y (b j)) from rfl,
    fderiv_comp x L.differentiableAt (hd.clm_apply (differentiableAt_const _)),
    L.fderiv, fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rfl

lemma mixed_jacobian_curl {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (b c : Module.Basis ι ℝ E) (i l m : ι) :
    fderiv ℝ (mixed_jacobianMatrix b c f) x (b i) l m =
      fderiv ℝ (mixed_jacobianMatrix b c f) x (b m) l i := by
  rw [mixed_fderiv_jacobian_apply hf, mixed_fderiv_jacobian_apply hf,
    (hf.isSymmSndFDerivAt (by norm_num)).eq]
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MixedPiolaIdentity
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
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma mixed_piola_identity {f : E → E} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (b c : Module.Basis ι ℝ E) (hx : IsUnit (mixed_jacobianMatrix b c f x).det) (k : ι) :
    ∑ i, fderiv ℝ (fun y => (mixed_jacobianMatrix b c f y).det *
      (mixed_jacobianMatrix b c f y)⁻¹ i k) x (b i) = 0 :=
  piola_of_curl b (mixed_differentiableAt_jacobian hf b c) hx (mixed_jacobian_curl hf b c) k

omit [FiniteDimensional ℝ E] in
lemma mixed_fderiv_comp_basis {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hX : DifferentiableAt ℝ X (f x))
    (b c : Module.Basis ι ℝ E) (k i : ι) :
    fderiv ℝ (fun y => X (f y) k) x (b i) =
      ∑ m, mixed_jacobianMatrix b c f x m i * fderiv ℝ (fun z => X z k) (f x) (c m) := by
  have hk := differentiableAt_pi.mp hX k
  rw [show (fun y => X (f y) k) = (fun z => X z k) ∘ f from rfl,
    fderiv_comp x hk hf, ContinuousLinearMap.comp_apply,
    ← c.sum_repr (fderiv ℝ f x (b i))]
  simp only [map_sum, map_smul, smul_eq_mul, mixed_jacobianMatrix_apply]
  rfl

lemma mixed_piola_divergence {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hX : DifferentiableAt ℝ X (f x))
    (b c : Module.Basis ι ℝ E) (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    ∑ i, fderiv ℝ (fun y => ∑ k, (mixed_jacobianMatrix b c f y).det *
      (mixed_jacobianMatrix b c f y)⁻¹ i k * X (f y) k) x (b i) =
      (mixed_jacobianMatrix b c f x).det * ∑ k, fderiv ℝ (fun z => X z k) (f x) (c k) := by
  let J := mixed_jacobianMatrix b c f
  have hJ : DifferentiableAt ℝ J x := mixed_differentiableAt_jacobian hf b c
  have hd : DifferentiableAt ℝ (fun y => (J y).det) x :=
    (differentiable_det _).comp x hJ
  have hB := differentiableAt_matrix_inv hJ hx
  have hC (i k : ι) : DifferentiableAt ℝ (fun y => (J y).det * (J y)⁻¹ i k) x :=
    hd.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hB i) k)
  have hf' := hf.differentiableAt (by norm_num)
  have hY (k : ι) : DifferentiableAt ℝ (fun y => X (f y) k) x :=
    (differentiableAt_pi.mp hX k).comp x hf'
  change (∑ i, fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k)
    x (b i)) = _
  have hexp (i : ι) : fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k)
      x (b i) = ∑ k, ((J x).det * (J x)⁻¹ i k * fderiv ℝ (fun y => X (f y) k) x (b i) +
        X (f x) k * fderiv ℝ (fun y => (J y).det * (J y)⁻¹ i k) x (b i)) := by
    erw [fderiv_fun_sum (u := Finset.univ) (A := fun k y =>
      (J y).det * (J y)⁻¹ i k * X (f y) k) (fun k _ => (hC i k).mul (hY k))]
    simp only [fderiv_fun_mul (hC _ _) (hY _), _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp_rw [hexp, Finset.sum_add_distrib]
  have hz : (∑ i, ∑ k, X (f x) k * fderiv ℝ (fun y => (J y).det * (J y)⁻¹ i k) x (b i)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    rw [← Finset.mul_sum, mixed_piola_identity hf b c hx k, mul_zero]
  rw [hz, add_zero]
  simp_rw [mixed_fderiv_comp_basis hf' hX b c, mul_assoc, ← Finset.mul_sum]
  congr 1
  let D : Matrix ι ι ℝ := fun k m => fderiv ℝ (fun z => X z k) (f x) (c m)
  have ht : (∑ i, ∑ k, (J x)⁻¹ i k * ∑ m, J x m i * D k m) =
      Matrix.trace ((J x)⁻¹ * (D * J x)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    congr 1
    ext i
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  change (∑ i, ∑ k, (J x)⁻¹ i k * ∑ m, J x m i * D k m) = ∑ k, D k k
  rw [ht, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hx,
    Matrix.mul_one]
  rfl
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_MixedPiolaDivergenceAbs
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

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
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma mixed_piola_divergence_abs {f : E → E} {X : E → ι → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hX : DifferentiableAt ℝ X (f x))
    (b c : Module.Basis ι ℝ E) (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    ∑ i, fderiv ℝ (fun y => ∑ k, |(mixed_jacobianMatrix b c f y).det| *
      (mixed_jacobianMatrix b c f y)⁻¹ i k * X (f y) k) x (b i) =
      |(mixed_jacobianMatrix b c f x).det| * ∑ k, fderiv ℝ (fun z => X z k) (f x) (c k) := by
  let J := mixed_jacobianMatrix b c f
  have hJ : DifferentiableAt ℝ J x := mixed_differentiableAt_jacobian hf b c
  have hd : ContinuousAt (fun y => (J y).det) x :=
    ((differentiable_det _).comp x hJ).continuousAt
  obtain ⟨sgn, hcx, hcy⟩ := local_abs_multiplier hd (isUnit_iff_ne_zero.mp hx)
  have hh (i : ι) : fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x =
      sgn • fderiv ℝ (fun y => ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) x := by
    have he : (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) =ᶠ[𝓝 x]
        (fun y => sgn * ∑ k, (J y).det * (J y)⁻¹ i k * X (f y) k) := by
      filter_upwards [hcy] with y hy
      simp only [hy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he.fderiv_eq]
    have hf' := hf.differentiableAt (by norm_num)
    have hB := differentiableAt_matrix_inv hJ hx
    have hd' : DifferentiableAt ℝ (fun y => (J y).det) x :=
      (differentiable_det _).comp x hJ
    exact fderiv_const_mul (DifferentiableAt.fun_sum (fun k _ =>
      (hd'.mul (differentiableAt_pi.mp (differentiableAt_pi.mp hB i) k)).mul
        ((differentiableAt_pi.mp hX k).comp x hf'))) sgn
  change (∑ i, fderiv ℝ (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * X (f y) k) x (b i)) = _
  simp_rw [hh, _root_.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mixed_piola_divergence hf hX b c hx]
  change sgn * ((J x).det * _) = |(J x).det| * _
  rw [hcx, mul_assoc]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldChartPush
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [NormedSpace ℝ E] [NormedSpace ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma manifoldChartPush_apply (p : M) (f : E → V) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    manifoldChartPush p f ((chartAt E p).symm y) = f y := by
  simp only [manifoldChartPush, Set.indicator_of_mem ((chartAt E p).map_target hy),
    Function.comp_apply, (chartAt E p).right_inv hy]

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CoordinateMetricFlux
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma pullbackMetricMatrix_density (b c : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (f : E → E) (x : E) :
    Real.sqrt (pullbackMetricMatrix b c G f x).det =
      |(mixed_jacobianMatrix b c f x).det| * Real.sqrt (G (f x)).det := by
  have he : (pullbackMetricMatrix b c G f x).det =
      (mixed_jacobianMatrix b c f x).det ^ 2 * (G (f x)).det := by
    simp only [pullbackMetricMatrix,Matrix.det_mul,Matrix.det_transpose]
    ring
  rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

omit [FiniteDimensional ℝ E] in
lemma pullbackMetricMatrix_inverse_left (b c : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (f : E → E) {x : E}
    (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    (pullbackMetricMatrix b c G f x)⁻¹ * (mixed_jacobianMatrix b c f x).transpose =
      (mixed_jacobianMatrix b c f x)⁻¹ * (G (f x))⁻¹ := by
  have ht : IsUnit (mixed_jacobianMatrix b c f x).transpose.det := by
    simpa only [Matrix.det_transpose] using hx
  rw [pullbackMetricMatrix,Matrix.mul_inv_rev,Matrix.mul_inv_rev,
    Matrix.mul_assoc,Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ht,
    Matrix.mul_one]

omit [FiniteDimensional ℝ E] in
lemma mixed_fderiv_comp_scalar {f : E → E} {u : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u (f x))
    (b c : Module.Basis ι ℝ E) (i : ι) :
    fderiv ℝ (u ∘ f) x (b i) =
      ∑ k, fderiv ℝ u (f x) (c k) * mixed_jacobianMatrix b c f x k i := by
  rw [fderiv_comp x hu hf,ContinuousLinearMap.comp_apply,
    ← c.sum_repr (fderiv ℝ f x (b i))]
  simp only [map_sum,map_smul,smul_eq_mul,mixed_jacobianMatrix_apply,
    Module.Basis.coord_apply,mul_comm]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricFlux_pullback {f : E → E} {u : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u (f x))
    (b c : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ)
    (hx : IsUnit (mixed_jacobianMatrix b c f x).det) (i : ι) :
    coordinateMetricFlux b (pullbackMetricMatrix b c G f) (u ∘ f) x i =
      ∑ k, |(mixed_jacobianMatrix b c f x).det| * (mixed_jacobianMatrix b c f x)⁻¹ i k *
        coordinateMetricFlux c G u (f x) k := by
  let d : ι → ℝ := fun j => fderiv ℝ u (f x) (c j)
  have hh := congrArg (fun A : Matrix ι ι ℝ => A.mulVec d i)
    (pullbackMetricMatrix_inverse_left b c G f hx)
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec] at hh
  simp only [coordinateMetricFlux,mixed_fderiv_comp_scalar hf hu b c,
    pullbackMetricMatrix_density b c G f]
  have hs : (∑ j, (pullbackMetricMatrix b c G f x)⁻¹ i j *
      ∑ k, d k * mixed_jacobianMatrix b c f x k j) =
      ∑ k, (mixed_jacobianMatrix b c f x)⁻¹ i k * ∑ j, (G (f x))⁻¹ k j * d j := by
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,mul_comm] using hh
  change (_ * _) * (∑ j, (pullbackMetricMatrix b c G f x)⁻¹ i j *
    ∑ k, d k * mixed_jacobianMatrix b c f x k j) = _
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [d]
  ring

omit [FiniteDimensional ℝ E] in
lemma differentiableAt_coordinateMetricFlux {u : E → ℝ} {G : E → Matrix ι ι ℝ}
    {x : E} (hu : ContDiffAt ℝ 2 u x) (hG : DifferentiableAt ℝ G x)
    (hx : 0 < (G x).det) (b : Module.Basis ι ℝ E) :
    DifferentiableAt ℝ (coordinateMetricFlux b G u) x := by
  have hd : DifferentiableAt ℝ (fun y => (G y).det) x :=
    (differentiable_det _).comp x hG
  have hi := differentiableAt_matrix_inv hG (isUnit_iff_ne_zero.mpr hx.ne')
  have hu' := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply differentiableAt_pi.mpr
  intro i
  apply (hd.sqrt hx.ne').mul
  apply DifferentiableAt.fun_sum
  intro j hj
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hi i) j).mul
    (hu'.clm_apply (differentiableAt_const _))

theorem coordinateMetricLaplacian_pullback {f : E → E} {u : E → ℝ}
    {G : E → Matrix ι ι ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hu : ContDiffAt ℝ 2 u (f x))
    (hG : DifferentiableAt ℝ G (f x)) (hpos : 0 < (G (f x)).det)
    (b c : Module.Basis ι ℝ E) (hx : IsUnit (mixed_jacobianMatrix b c f x).det) :
    coordinateMetricLaplacian b (pullbackMetricMatrix b c G f) (u ∘ f) x =
      coordinateMetricLaplacian c G u (f x) := by
  let J := mixed_jacobianMatrix b c f
  have hJ : ContinuousAt (fun y => (J y).det) x :=
    ((differentiable_det _).comp x (mixed_differentiableAt_jacobian hf b c)).continuousAt
  have hJn : ∀ᶠ y in 𝓝 x, IsUnit (J y).det := by
    filter_upwards [hJ.eventually_ne (isUnit_iff_ne_zero.mp hx)] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have huN : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u (f y) :=
    hf.continuousAt (hu.eventually (by simp))
  have hflux (i : ι) : (fun y => coordinateMetricFlux b (pullbackMetricMatrix b c G f) (u ∘ f) y i)
      =ᶠ[𝓝 x] (fun y => ∑ k, |(J y).det| * (J y)⁻¹ i k * coordinateMetricFlux c G u (f y) k) := by
    filter_upwards [hf.eventually (by simp),huN,hJn] with y hy hfyu hyJ
    exact coordinateMetricFlux_pullback (hy.differentiableAt (by norm_num))
      (hfyu.differentiableAt (by norm_num)) b c G hyJ i
  have hdiv := mixed_piola_divergence_abs hf (differentiableAt_coordinateMetricFlux hu hG hpos c) b c hx
  simp only [coordinateMetricLaplacian]
  simp_rw [(hflux _).fderiv_eq]
  rw [pullbackMetricMatrix_density,hdiv]
  have hn : |(J x).det| ≠ 0 := abs_ne_zero.mpr (isUnit_iff_ne_zero.mp hx)
  change (_ * _)⁻¹ * (|(J x).det| * _) = _
  rw [_root_.mul_inv_rev]
  change (Real.sqrt (G (f x)).det)⁻¹ * (|(J x).det|)⁻¹ * (|(J x).det| * _) = _
  rw [mul_assoc,inv_mul_cancel_left₀ hn]
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

omit [FiniteDimensional ℝ E] in
lemma selfMetricFlat_apply (g : SmoothMetric E E) (x v w : E) :
    selfMetricFlat g x v w = g.inner x v w := rfl


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LinearMetricForm
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
lemma linearPullbackMetric_flat (g : SmoothMetric E E) (L : F ≃L[ℝ] E) (x v w : F) :
    selfMetricFlat (linearPullbackMetric g L) x v w = selfMetricFlat g (L x) (L v) (L w) := by
  rw [selfMetricFlat_apply]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma fderiv_linearEquiv_comp {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (L : F ≃L[ℝ] E) (x v : F) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf.differentiable (by simp) _) L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
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
open Set Filter Matrix Manifold
open scoped Topology ContDiff
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma bilinearCoordinateMatrix_comp (b c : Module.Basis ι ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E) :
    bilinearCoordinateMatrix b (T.bilinearComp A A) =
      (LinearMap.toMatrix b c A.toLinearMap).transpose * bilinearCoordinateMatrix c T *
        LinearMap.toMatrix b c A.toLinearMap := by
  ext i j
  change T (A (b i)) (A (b j)) = _
  rw [← c.sum_repr (A (b i)), ← c.sum_repr (A (b j))]
  simp only [map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix_apply, bilinearCoordinateMatrix,
    ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_reindex (e : ι ≃ κ) (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) (u : E → ℝ) (x : E) :
    coordinateMetricLaplacian (b.reindex e) (fun y => Matrix.reindex e e (G y)) u x =
      coordinateMetricLaplacian b G u x := by
  have hf (y : E) (i : κ) :
      coordinateMetricFlux (b.reindex e) (fun y => Matrix.reindex e e (G y)) u y i =
        coordinateMetricFlux b G u y (e.symm i) := by
    simp only [coordinateMetricFlux]
    rw [Matrix.det_reindex_self,Matrix.inv_reindex]
    simp only [Matrix.reindex_apply,Module.Basis.reindex_apply,Matrix.submatrix_apply]
    exact congrArg (fun t : ℝ => Real.sqrt (G y).det * t)
      (e.symm.sum_comp (fun j => (G y)⁻¹ (e.symm i) j * fderiv ℝ u y (b j)))
  simp only [coordinateMetricLaplacian,Matrix.det_reindex_self]
  simp_rw [hf]
  simp only [Module.Basis.reindex_apply]
  exact congrArg (fun t : ℝ => (Real.sqrt (G x).det)⁻¹ * t)
    (e.symm.sum_comp (fun i => fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i)))

omit [FiniteDimensional ℝ E] in
lemma mixed_jacobianMatrix_id_isUnit (b c : Module.Basis ι ℝ E) (x : E) :
    IsUnit (mixed_jacobianMatrix b c (id : E → E) x).det := by
  have hp : LinearMap.toMatrix c b (LinearMap.id : E →ₗ[ℝ] E) *
      LinearMap.toMatrix b c (LinearMap.id : E →ₗ[ℝ] E) = 1 := by
    rw [← LinearMap.toMatrix_comp,LinearMap.id_comp,LinearMap.toMatrix_id]
  have hdet := congrArg Matrix.det hp
  rw [Matrix.det_mul,Matrix.det_one] at hdet
  apply isUnit_iff_ne_zero.mpr
  rw [mixed_jacobianMatrix,fderiv_id]
  exact right_ne_zero_of_mul_eq_one hdet

lemma coordinateVector_self (p y : E) (i : CoordIndex E) :
    coordinateVector p y i = Module.finBasis ℝ E i := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (id : E → E) y (Module.finBasis ℝ E i) = _
  rw [mfderiv_id]
  rfl

lemma metricCoefficients_self (g : SmoothMetric E E) (p y : E) (i j : CoordIndex E) :
    metricCoefficients g p y i j = g.inner y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) := by
  simp only [metricCoefficients,coordinateVector_self]
  rfl

lemma laplaceBeltrami_self (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    laplaceBeltrami g u x =
      coordinateMetricLaplacian (Module.finBasis ℝ E) (metricCoefficients g x) u x := by
  simp only [laplaceBeltrami,coordinateMetricLaplacian,coordinateMetricFlux,
    chartAt_self_eq,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,
    Function.comp_id,id_eq]


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
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
lemma bilinearCoordinateMatrix_posDef (b : Module.Basis ι ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ v w, T v w = T w v)
    (hp : ∀ v, v ≠ 0 → 0 < T v v) : (bilinearCoordinateMatrix b T).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    exact hs _ _
  · intro a ha
    have hn : b.equivFun.symm a ≠ 0 := by
      intro h
      exact ha (b.equivFun.symm.injective (h.trans (map_zero _).symm))
    have h := hp _ hn
    rw [Module.Basis.equivFun_symm_apply] at h
    simpa [bilinearCoordinateMatrix,map_sum,map_smul,_root_.sum_apply,
      _root_.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,Finset.mul_sum,
      Finset.sum_mul,mul_assoc,mul_comm,mul_left_comm,hs] using h

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
lemma contDiff_bilinearCoordinateMatrix (b : Module.Basis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (fun x => bilinearCoordinateMatrix b (T x)) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (hT.clm_apply contDiff_const).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
lemma selfMetricMatrix_pullback (g : SmoothMetric E E) (b c : Module.Basis ι ℝ E)
    (f : E → E) (x : E) :
    pullbackMetricMatrix b c (fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)) f x =
      bilinearCoordinateMatrix b ((selfMetricFlat g (f x)).bilinearComp
        (fderiv ℝ f x) (fderiv ℝ f x)) :=
  (bilinearCoordinateMatrix_comp b c _ _).symm

omit [FiniteDimensional ℝ E] in
lemma selfMetricMatrix_change_basis (g : SmoothMetric E E) (b c : Module.Basis ι ℝ E) :
    pullbackMetricMatrix b c (fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)) id =
      (fun y => bilinearCoordinateMatrix b (selfMetricFlat g y)) := by
  funext x
  rw [selfMetricMatrix_pullback,fderiv_id]
  rfl

lemma coordinateMetricLaplacian_basis_independent (g : SmoothMetric E E)
    (b c : Module.Basis ι ℝ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    coordinateMetricLaplacian b (fun y => bilinearCoordinateMatrix b (selfMetricFlat g y)) u x =
      coordinateMetricLaplacian c (fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)) u x := by
  have hG := (contDiff_bilinearCoordinateMatrix c (contDiff_selfMetricFlat g)).differentiable (by simp) x
  have hp := (bilinearCoordinateMatrix_posDef c (selfMetricFlat g x)
    (selfMetricFlat_symm g x) (fun v hv => selfMetricFlat_pos g x hv)).det_pos
  have h := coordinateMetricLaplacian_pullback (f := (id : E → E)) contDiffAt_id hu hG hp b c
    (mixed_jacobianMatrix_id_isUnit b c x)
  rwa [selfMetricMatrix_change_basis,Function.comp_id] at h

theorem laplaceBeltrami_self_any_basis (g : SmoothMetric E E)
    (b : Module.Basis ι ℝ E) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    laplaceBeltrami g u x =
      coordinateMetricLaplacian b (fun y => bilinearCoordinateMatrix b (selfMetricFlat g y)) u x := by
  let e : CoordIndex E ≃ ι := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b)
  let c := (Module.finBasis ℝ E).reindex e
  have he (y : E) : Matrix.reindex e e (metricCoefficients g x y) =
      bilinearCoordinateMatrix c (selfMetricFlat g y) := by
    ext i j
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,bilinearCoordinateMatrix,
      c,Module.Basis.reindex_apply,selfMetricFlat_apply,metricCoefficients_self]
  rw [laplaceBeltrami_self,← coordinateMetricLaplacian_reindex e]
  simp_rw [he]
  exact coordinateMetricLaplacian_basis_independent g c b hu

end

section
open Set Filter Function Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma linearPullbackMetric_laplace (g : SmoothMetric E E) (L : F ≃L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : F) :
    laplaceBeltrami (linearPullbackMetric g L) (f ∘ L) x = laplaceBeltrami g f (L x) := by
  classical
  let b := Module.finBasis ℝ F
  let c := b.map L.toLinearEquiv
  let G := fun y => bilinearCoordinateMatrix c (selfMetricFlat g y)
  have hmat : (fun y => bilinearCoordinateMatrix b (selfMetricFlat (linearPullbackMetric g L) y)) = G ∘ L := by
    funext y
    ext i j
    exact linearPullbackMetric_flat g L y (b i) (b j)
  have hcb (i : CoordIndex F) : c i=L (b i) := rfl
  have hflux (i : CoordIndex F) : (fun y => coordinateMetricFlux b (G ∘ L) (f ∘ L) y i) =
      (fun y => coordinateMetricFlux c G f y i) ∘ L := by
    funext y
    simp only [coordinateMetricFlux,Function.comp_apply,fderiv_linearEquiv_comp hf L,hcb]
  have h2 : ContDiff ℝ 2 f := hf.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))
  have h2c : ContDiff ℝ 2 (f ∘ L) := h2.comp L.contDiff
  rw [laplaceBeltrami_self_any_basis _ b h2c.contDiffAt,
    laplaceBeltrami_self_any_basis _ c h2.contDiffAt,hmat]
  dsimp only [coordinateMetricLaplacian]
  change (Real.sqrt (G (L x)).det)⁻¹ * _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hflux]
  have hG := (contDiff_bilinearCoordinateMatrix c (contDiff_selfMetricFlat g)).differentiable (by simp) (L x)
  have hp := (bilinearCoordinateMatrix_posDef c (selfMetricFlat g (L x))
    (selfMetricFlat_symm g (L x)) (fun v hv => selfMetricFlat_pos g (L x) hv)).det_pos
  have hdi : DifferentiableAt ℝ (fun y => coordinateMetricFlux c G f y i) (L x) :=
    differentiableAt_pi.mp (differentiableAt_coordinateMetricFlux h2.contDiffAt hG hp c) i
  rw [fderiv_comp x hdi L.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,hcb]
  rfl
end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem laplaceBeltrami_chart_metric (g : SmoothMetric E M) (ĝ : SmoothMetric E E)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) {u : M → ℝ} {f : E → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hg : ∀ᶠ z in 𝓝 y, ∀ v w : E, ĝ.inner z v w = g.inner ((chartAt E p).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z w))
    (hf : u ∘ (chartAt E p).symm =ᶠ[𝓝 y] f) :
    laplaceBeltrami g u ((chartAt E p).symm y) = laplaceBeltrami ĝ f y := by
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  have ha : metricCoefficients ĝ y =ᶠ[𝓝 y] metricCoefficients g p := by
    filter_upwards [hg] with z hz
    ext i j
    rw [metricCoefficients_self]
    exact hz _ _
  have hflux : ∀ i, (fun z => metricFlux g u p z i) =ᶠ[𝓝 y]
      (fun z => metricFlux ĝ f y z i) := by
    intro i
    filter_upwards [ha, hf.fderiv (𝕜 := ℝ)] with z hz hdz
    simp only [metricFlux, hz, hdz, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
    rfl
  change localLaplacian g u p y = localLaplacian ĝ f y y
  simp only [localLaplacian, ← ha.eq_of_nhds]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hflux i).fderiv_eq]

theorem laplaceBeltrami_manifoldChartPush [T2Space M]
    (g : SmoothMetric E M) (ĝ : SmoothMetric E E) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt E p).target)
    (hg : ∀ᶠ z in 𝓝 y, ∀ v w : E, ĝ.inner z v w = g.inner ((chartAt E p).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z w)) :
    laplaceBeltrami g (manifoldChartPush p f) ((chartAt E p).symm y) =
      laplaceBeltrami ĝ f y := by
  apply laplaceBeltrami_chart_metric g ĝ p hy (contMDiff_manifoldChartPush p hf hc hs) hg
  filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
  exact manifoldChartPush_apply p f hz

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ThreeRadiusNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
attribute [local instance] OAI.YauCounterexamples.threeChartNormedSpace
local instance threeChartContinuousSMul_rc93c1c_1 : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
lemma threeChartMetric_selfFlat (g : SmoothMetric ThreeModel ThreeManifold) (p : ThreeManifold) (y : ThreeModel) :
    selfMetricFlat (threeChartMetric g p) y = chartMetricForm g p y := by
  ext v w
  rw [selfMetricFlat_apply]
  rfl
end


open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
attribute [local instance] OAI.YauCounterexamples.threeLiftNormedSpace
local instance threeLiftContinuousSMul_rc93c1c_1 : ContinuousSMul ℝ ThreeModel :=
  IsBoundedSMul.continuousSMul
lemma threeWaveLift_laplacian_oai (g : SmoothMetric ThreeModel ThreeManifold)
    {u : NormalWaveSpace → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (y : NormalWaveSpace) :
    laplaceBeltrami g (threeWaveLift u) (threeNormalInv y)=laplaceBeltrami (threeNormalMetricOf g) u y := by
  have he : (u ∘ threeNormalEquiv.symm) ∘ threeNormalEquiv=u := by funext z; simp
  have ht := linearPullbackMetric_laplace (threeChartMetric g threeProfileCenter) threeNormalEquiv
    (hu.comp threeNormalEquiv.symm.contDiff) y
  rw [he] at ht
  change _ = laplaceBeltrami (linearPullbackMetric (threeChartMetric g threeProfileCenter) threeNormalEquiv) u y
  rw [ht]
  apply laplaceBeltrami_manifoldChartPush g (threeChartMetric g threeProfileCenter) threeProfileCenter
    (by rw [three_chart_target]; trivial) (hu.comp threeNormalEquiv.symm.contDiff)
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _)
  filter_upwards [] with z v w
  rw [←selfMetricFlat_apply,threeChartMetric_selfFlat,chartMetricForm_pairing]
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.threeWaveLift_laplacian_oai := @OAI.YauCounterexamples.threeWaveLift_laplacian_oai
