-- Prove2me | solution 1 for OAI.YauCounterexamples.normalChartWave_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:37:32.98201+00:00
-- url     : https://prove2.me/submissions/e820e0d0-d81a-437b-aec3-acb1b9229ad4

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateMetricFirstCoefficient
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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_expansion (b : Module.Basis ι ℝ E)
    {G : E → Matrix ι ι ℝ} {u : E → ℝ} {x : E}
    (hG : DifferentiableAt ℝ G x) (hu : ContDiffAt ℝ 2 u x) (hp : 0 < (G x).det) :
    coordinateMetricLaplacian b G u x =
      (∑ i, ∑ j, (G x)⁻¹ i j * fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i)) +
        ∑ j, coordinateMetricFirstCoefficient b G x j * fderiv ℝ u x (b j) := by
  let ρ := fun y => Real.sqrt (G y).det
  have hρ : DifferentiableAt ℝ ρ x := ((differentiable_det _).comp x hG).sqrt hp.ne'
  have hAi := differentiableAt_matrix_inv hG (isUnit_iff_ne_zero.mpr hp.ne')
  have hA (i j : ι) : DifferentiableAt ℝ (fun y => (G y)⁻¹ i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hAi i) j
  have hv := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (i : ι) : (fun y => coordinateMetricFlux b G u y i) =
      fun y => ∑ j, (ρ y * (G y)⁻¹ i j) * fderiv ℝ u y (b j) := by
    funext y
    simp only [coordinateMetricFlux,ρ,Finset.mul_sum,mul_assoc]
  have hder (i : ι) : fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i) =
      ∑ j, ((ρ x * (G x)⁻¹ i j) * fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i) +
        fderiv ℝ u x (b j) * fderiv ℝ (fun y => ρ y * (G y)⁻¹ i j) x (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j y => (ρ y * (G y)⁻¹ i j) * fderiv ℝ u y (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun y => ρ y * (G y)⁻¹ i j)
      (d := fun y => fderiv ℝ u y (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  change (ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => coordinateMetricFlux b G u y i) x (b i) = _
  simp_rw [hder,Finset.sum_add_distrib]
  rw [mul_add,Finset.mul_sum,Finset.mul_sum]
  have hn : ρ x ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hmain : (∑ i, (ρ x)⁻¹ * ∑ j, ρ x * (G x)⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i)) =
      ∑ i, ∑ j, (G x)⁻¹ i j * fderiv ℝ (fun y => fderiv ℝ u y (b j)) x (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinateMetricFirstCoefficient,ρ,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmoothFiniteWaveSum
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma waveDeriv_congr_eventually {f h : E → ℂ} {x : E} (he : f =ᶠ[𝓝 x] h) (v : E) :
    waveDeriv v f =ᶠ[𝓝 x] waveDeriv v h := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : E →L[ℝ] ℂ => L v) hy

lemma waveCoordinateOperator_congr_eventually (e : ι → E) (g : ι → ι → E → ℂ)
    (b : ι → E → ℂ) {V W : E → ℂ} {x : E} (hV : V =ᶠ[𝓝 x] W) :
    waveCoordinateOperator e g b V =ᶠ[𝓝 x] waveCoordinateOperator e g b W := by
  have hv : ∀ᶠ y in 𝓝 x, ∀ i, waveDeriv (e i) V y = waveDeriv (e i) W y :=
    eventually_all.mpr (fun i => waveDeriv_congr_eventually hV (e i))
  have hvv : ∀ᶠ y in 𝓝 x, ∀ i j,
      waveDeriv (e i) (waveDeriv (e j) V) y = waveDeriv (e i) (waveDeriv (e j) W) y :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j =>
      waveDeriv_congr_eventually (waveDeriv_congr_eventually hV (e j)) (e i)))
  filter_upwards [hv,hvv] with y hvy hvvy
  simp only [waveCoordinateOperator,hvy,hvvy]

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
open Set Filter
open scoped Topology ContDiff

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

attribute [local instance] OAI.YauCounterexamples.normalDualNorm
attribute [local instance] OAI.YauCounterexamples.normalFormNorm
attribute [local instance] OAI.YauCounterexamples.normalDualSpace
attribute [local instance] OAI.YauCounterexamples.normalFormSpace
local instance normalTriNorm_re890be_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
omit [FiniteDimensional ℝ E] in
lemma contDiff_normalJetMap (p : E) (A : E →L[ℝ] E) (C : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (normalJetMap p A C) :=
  (contDiff_const.add A.contDiff).sub ((C.contDiff.clm_apply contDiff_id).const_smul (1/2 : ℝ))

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

lemma normalMetricTensor_is_pullback (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (x v w : E) :
    normalMetricTensor g p A x v w = selfMetricFlat g
      (normalJetMap p A ((metricChristoffel g p).bilinearComp A A) x)
      (fderiv ℝ (normalJetMap p A ((metricChristoffel g p).bilinearComp A A)) x v)
      (fderiv ℝ (normalJetMap p A ((metricChristoffel g p).bilinearComp A A)) x w) := by
  rw [fderiv_normalJetMap p A _ (fun v w => metricChristoffel_symm g p (A v) (A w))]
  rfl

local instance normalTriSpace_re890be_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
lemma contDiff_normalMetricTensor_apply (g : SmoothMetric E E) (p : E)
    (A : E →L[ℝ] E) (v w : E) :
    ContDiff ℝ ∞ (fun x => normalMetricTensor g p A x v w) := by
  let C := (metricChristoffel g p).bilinearComp A A
  have hF := contDiff_normalJetMap p A C
  have hV (v : E) : ContDiff ℝ ∞ (fun x => (A - C x) v) :=
    (contDiff_const.sub C.contDiff).clm_apply contDiff_const
  exact (((contDiff_selfMetricFlat g).comp hF).clm_apply (hV v)).clm_apply (hV w)


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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
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
open scoped Topology ContDiff

variable {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι] [DecidableEq ι]
lemma contDiff_matrix_det (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) :
    ContDiff ℝ ∞ (fun p => (A p).det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hA _ _

lemma contDiff_matrix_adjugate (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) (i j : ι) :
    ContDiff ℝ ∞ (fun p => (A p).adjugate i j) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro k _
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hA _ _

lemma contDiffOn_matrix_inv (A : P → Matrix ι ι ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun p => A p i j)) (i j : ι) :
    ContDiffOn ℝ ∞ (fun p => (A p)⁻¹ i j) {p | (A p).det ≠ 0} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_matrix_det A hA).contDiffOn.inv (fun _ hp => hp)).mul
    (contDiff_matrix_adjugate A hA i j).contDiffOn

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
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
section Density
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma density_first_derivative {d a : E → ℝ} {x : E}
    (hd : DifferentiableAt ℝ d x) (ha : DifferentiableAt ℝ a x)
    (hx : 0 < d x) (v : E) :
    (Real.sqrt (d x))⁻¹ * fderiv ℝ (fun y => Real.sqrt (d y) * a y) x v =
      fderiv ℝ a x v + (1/2 : ℝ) * a x * (d x)⁻¹ * fderiv ℝ d x v := by
  erw [fderiv_fun_mul (hd.sqrt hx.ne') ha, _root_.add_apply]
  simp only [_root_.smul_apply, smul_eq_mul, fderiv_sqrt hd hx.ne']
  have hs : Real.sqrt (d x) ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hs2 : Real.sqrt (d x) ^ 2 = d x := Real.sq_sqrt hx.le
  field_simp
  rw [hs2]
  ring
end Density

lemma normalWaveDensity_firstCoefficient (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {x : NormalWaveSpace}
    (hx : 0 < (normalWaveMetric g q x).det) (j : Fin 3) :
    (Real.sqrt (normalWaveMetric g q x).det)⁻¹ *
      ∑ i, fderiv ℝ (fun y => Real.sqrt (normalWaveMetric g q y).det *
        (normalWaveMetric g q y)⁻¹ i j) x (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      normalWaveFirstCoefficient g q x j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hG (i j : Fin 3) : ContDiff ℝ ∞ (fun y => normalWaveMetric g q y i j) :=
    (contDiff_normalMetricTensor_apply g q.1 q.2
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
  have hd := (contDiff_matrix_det _ hG).differentiable (by simp) x
  have hO : IsOpen {y : NormalWaveSpace | (normalWaveMetric g q y).det ≠ 0} :=
    isOpen_ne_fun (contDiff_matrix_det _ hG).continuous continuous_const
  have ha := (contDiffOn_matrix_inv (normalWaveMetric g q) hG i j x hx.ne').contDiffAt
    (hO.mem_nhds hx.ne')
  exact density_first_derivative hd (ha.differentiableAt (by simp)) hx _

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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

lemma normalWaveMetric_pullback (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) :
    normalWaveMetric g q = pullbackMetricMatrix
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (fun y => bilinearCoordinateMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (selfMetricFlat g y))
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) := by
  funext x
  rw [selfMetricMatrix_pullback]
  ext i j
  exact normalMetricTensor_is_pullback g q.1 q.2 x _ _

theorem laplaceBeltrami_normal_coordinates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {u : NormalWaveSpace → ℝ} {x : NormalWaveSpace}
    (hu : ContDiffAt ℝ 2 u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
    (hx : IsUnit (mixed_jacobianMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x).det) :
    coordinateMetricLaplacian (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (normalWaveMetric g q)
      (u ∘ normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x =
      laplaceBeltrami g u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  rw [laplaceBeltrami_self_any_basis g b hu,normalWaveMetric_pullback]
  exact coordinateMetricLaplacian_pullback
    ((contDiff_normalJetMap _ _ _).of_le (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt hu
    ((contDiff_bilinearCoordinateMatrix b (contDiff_selfMetricFlat g)).differentiable (by simp) _)
    ((bilinearCoordinateMatrix_posDef b _ (selfMetricFlat_symm g _) (fun v hv => selfMetricFlat_pos g _ hv)).det_pos)
    b b hx
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
section ComplexCoordinate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma complexCoordinateMetricLaplacian_expansion (b : Module.Basis ι ℝ E)
    {G : E → Matrix ι ι ℝ} {u : E → ℂ} {x : E}
    (hG : DifferentiableAt ℝ G x) (hu : ContDiffAt ℝ 2 u x) (hp : 0 < (G x).det) :
    complexCoordinateMetricLaplacian b G u x =
      waveCoordinateOperator b (fun i j y => ((G y)⁻¹ i j : ℂ))
        (fun j y => (coordinateMetricFirstCoefficient b G y j : ℂ)) u x := by
  have hd := hu.differentiableAt (by norm_num)
  apply Complex.ext
  · change coordinateMetricLaplacian b G (Complex.re ∘ u) x = _
    have hur : ContDiffAt ℝ 2 (Complex.re ∘ u) x := Complex.reCLM.contDiff.contDiffAt.comp x hu
    rw [coordinateMetricLaplacian_expansion b hG hur hp]
    simp only [waveCoordinateOperator,waveDeriv,Complex.add_re,Complex.re_sum,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.reCLM hu _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.reCLM hd _
  · change coordinateMetricLaplacian b G (Complex.im ∘ u) x = _
    have hui : ContDiffAt ℝ 2 (Complex.im ∘ u) x := Complex.imCLM.contDiff.contDiffAt.comp x hu
    rw [coordinateMetricLaplacian_expansion b hG hui hp]
    simp only [waveCoordinateOperator,waveDeriv,Complex.add_im,Complex.im_sum,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.imCLM hu _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.imCLM hd _
end ComplexCoordinate

lemma normalWaveJacobian_isUnit (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) {x : NormalWaveSpace} (hx : 0 < (normalWaveMetric g q x).det) :
    IsUnit (mixed_jacobianMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [normalWaveMetric_pullback] at hx
  simp only [pullbackMetricMatrix,Matrix.det_mul,Matrix.det_transpose,hz,zero_mul,mul_zero] at hx
  exact lt_irrefl (0 : ℝ) hx

lemma normalWave_complexCoordinate_expansion
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (q : NormalWaveParameter)
    {v : NormalWaveSpace → ℂ} {x : NormalWaveSpace}
    (hv : ContDiffAt ℝ 2 v x) (hx : 0 < (normalWaveMetric g q x).det) :
    waveCoordinateOperator (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
      (fun j y => (normalWaveFirstCoefficient g q y j : ℂ)) v x =
    complexCoordinateMetricLaplacian (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (normalWaveMetric g q) v x := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hG : DifferentiableAt ℝ (normalWaveMetric g q) x := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (contDiff_normalMetricTensor_apply g q.1 q.2 _ _).differentiable (by simp) x
  rw [complexCoordinateMetricLaplacian_expansion b hG hv hx]
  have hcoef (j) : coordinateMetricFirstCoefficient b (normalWaveMetric g q) x j =
      normalWaveFirstCoefficient g q x j := normalWaveDensity_firstCoefficient g q hx j
  change waveCoordinateOperator b _ _ v x = waveCoordinateOperator b _ _ v x
  simp only [waveCoordinateOperator,hcoef]

lemma complexCoordinateMetricLaplacian_normal_coordinates
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (q : NormalWaveParameter)
    {u : NormalWaveSpace → ℂ} {x : NormalWaveSpace}
    (hu : ContDiffAt ℝ 2 u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
    (hx : 0 < (normalWaveMetric g q x).det) :
    complexCoordinateMetricLaplacian (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (normalWaveMetric g q)
      (u ∘ normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x =
      complexLaplaceBeltrami g u
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) := by
  have hJ := normalWaveJacobian_isUnit g q hx
  simp only [complexCoordinateMetricLaplacian,complexLaplaceBeltrami,← Function.comp_assoc]
  apply congrArg₂ Complex.mk
  · have hur : ContDiffAt ℝ 2 (Complex.re ∘ u)
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) :=
      Complex.reCLM.contDiff.contDiffAt.comp _ hu
    exact laplaceBeltrami_normal_coordinates g q hur hJ
  · have hui : ContDiffAt ℝ 2 (Complex.im ∘ u)
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) :=
      Complex.imCLM.contDiff.contDiffAt.comp _ hu
    exact laplaceBeltrami_normal_coordinates g q hui hJ

theorem complexLaplaceBeltrami_normal_coordinates
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace) (q : NormalWaveParameter)
    {u : NormalWaveSpace → ℂ} {x : NormalWaveSpace}
    (hu : ContDiffAt ℝ 2 u (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x))
    (hx : 0 < (normalWaveMetric g q x).det) :
    waveCoordinateOperator (EuclideanSpace.basisFun (Fin 3) ℝ)
      (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
      (fun j y => (normalWaveFirstCoefficient g q y j : ℂ))
      (u ∘ normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x =
      complexLaplaceBeltrami g u
        (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2) x) := by
  have hF : ContDiffAt ℝ 2
      (normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)) x :=
    ((contDiff_normalJetMap _ _ _).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  exact (normalWave_complexCoordinate_expansion g q (hu.comp x hF) hx).trans
    (complexCoordinateMetricLaplacian_normal_coordinates g q hu hx)
end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormalChartWave
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
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
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_apply (e : OpenPartialHomeomorph E F) (f : E → V)
    {x : E} (hx : x ∈ e.source) : smoothChartPush e f (e x) = f x := by
  simp only [smoothChartPush,Set.indicator_of_mem (e.map_source hx),Function.comp_apply,
    e.left_inv hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_support (e : OpenPartialHomeomorph E F) (f : E → V) :
    Function.support (smoothChartPush e f) ⊆ e '' tsupport f := by
  intro y hy
  have ht : y ∈ e.target := by
    by_contra hh
    exact hy (by simp [smoothChartPush,hh])
  refine ⟨e.symm y, subset_closure ?_,e.right_inv ht⟩
  simpa only [smoothChartPush,Set.indicator_of_mem ht,Function.comp_apply,
    Function.mem_support] using hy

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_tsupport (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : HasCompactSupport f) (hsub : tsupport f ⊆ e.source) :
    tsupport (smoothChartPush e f) ⊆ e '' tsupport f := by
  apply closure_minimal (smoothChartPush_support e f)
  exact (hf.image_of_continuousOn (e.continuousOn.mono hsub)).isClosed

lemma contDiff_smoothChartPush (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hsub : tsupport f ⊆ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (smoothChartPush e f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · have hg : smoothChartPush e f =ᶠ[𝓝 y] f ∘ e.symm := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact Set.indicator_of_mem hz _
    exact (hf.contDiffAt.comp y ((hi y hy).contDiffAt (e.open_target.mem_nhds hy))).congr_of_eventuallyEq hg
  · have hn : y ∉ e '' tsupport f := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hsub hx))
    have hs : y ∉ tsupport (smoothChartPush e f) := fun h => hn (smoothChartPush_tsupport e hc hsub h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hs)

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

lemma contDiff_normalChartWave (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (normalChartWave e f) := by
  apply contDiff_smoothChartPush e (hf.comp normalWaveEquiv.symm.contDiff)
    (hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph) _ hi
  change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
  rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
  intro x hx
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm x) hx

theorem normalChartWave_laplacian_oai (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : (e : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) {x : Fin 3 → ℝ}
    (hx : normalWaveEquiv x ∈ e.source)
    (hp : 0 < (normalWaveMetric g q (normalWaveEquiv x)).det) :
    complexLaplaceBeltrami g (normalChartWave e f) (e (normalWaveEquiv x)) =
      normalWavePiOperator g q f x := by
  have hu := contDiff_normalChartWave e hf hc hs hi
  have h1 : (normalChartWave e f ∘
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
      =ᶠ[𝓝 (normalWaveEquiv x)] (f ∘ normalWaveEquiv.symm) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    change normalChartWave e f (normalJetMap _ _ _ y) = f (normalWaveEquiv.symm y)
    rw [←he]
    exact smoothChartPush_apply e (f ∘ normalWaveEquiv.symm) hy
  have h2 := (waveCoordinateOperator_congr_eventually
    (EuclideanSpace.basisFun (Fin 3) ℝ)
    (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
    (fun j y => (normalWaveFirstCoefficient g q y j : ℂ)) h1).eq_of_nhds
  have h3 := complexLaplaceBeltrami_normal_coordinates g q
    (hu.of_le (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt hp
  rw [←he] at h3 h2
  exact h3.symm.trans h2



end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.normalChartWave_laplacian_oai := @OAI.YauCounterexamples.normalChartWave_laplacian_oai
