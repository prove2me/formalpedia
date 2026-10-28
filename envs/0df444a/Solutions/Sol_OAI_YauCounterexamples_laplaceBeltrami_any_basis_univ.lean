-- Prove2me | solution 1 for OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:18:15.464915+00:00
-- url     : https://prove2.me/submissions/5fe26483-9a53-4e37-95c5-97f9e4d53ce0

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A004
import Definitions.Def_OAIQ070A005
import Definitions.Def_OAIQ070A006

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


end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma bilinearCoordinateMatrix_posDef_normed (b : Module.Basis ι ℝ E)
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
lemma coordinateMetricLaplacian_change_basis_normed
    (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (hT : Differentiable ℝ T)
    (hs : ∀ x v w, T x v w=T x w v) (hp : ∀ x v, v≠0 → 0<T x v v)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    coordinateMetricLaplacian b (fun y => bilinearCoordinateMatrix b (T y)) u x =
      coordinateMetricLaplacian c (fun y => bilinearCoordinateMatrix c (T y)) u x := by
  classical
  let e : ι ≃ κ := Fintype.equivOfCardEq (by rw [←Module.finrank_eq_card_basis b,←Module.finrank_eq_card_basis c])
  let d := b.reindex e
  have hd (y : E) : Matrix.reindex e e (bilinearCoordinateMatrix b (T y)) = bilinearCoordinateMatrix d (T y) := by
    ext i j
    simp [d,Matrix.reindex_apply,Module.Basis.reindex_apply,bilinearCoordinateMatrix]
  rw [←coordinateMetricLaplacian_reindex e]
  simp_rw [hd]
  have hG : DifferentiableAt ℝ (fun y => bilinearCoordinateMatrix c (T y)) x :=
    differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
      ((hT x).clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hpos := (bilinearCoordinateMatrix_posDef_normed c (T x) (hs x) (hp x)).det_pos
  have hpb : pullbackMetricMatrix d c (fun y => bilinearCoordinateMatrix c (T y)) id =
      (fun y => bilinearCoordinateMatrix d (T y)) := by
    funext y
    rw [pullbackMetricMatrix, mixed_jacobianMatrix, fderiv_id]
    have he := bilinearCoordinateMatrix_comp d c (T y) (ContinuousLinearMap.id ℝ E)
    have hid : (T y).bilinearComp (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E) = T y := by
      ext v w
      rfl
    simpa only [hid, id_eq] using he.symm
  have h := coordinateMetricLaplacian_pullback (f:=(id:E→E)) contDiffAt_id hu hG hpos d c
    (mixed_jacobianMatrix_id_isUnit d c x)
  rwa [hpb,Function.comp_id] at h
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
lemma laplaceBeltrami_any_basis_univ_oai (g : SmoothMetric E M) (p : M)
    (ht : (chartAt E p).target=univ) (b : Module.Basis ι ℝ E)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) :
    laplaceBeltrami g u p = coordinateMetricLaplacian b
      (fun y => bilinearCoordinateMatrix b (chartMetricForm g p y))
      (u ∘ (chartAt E p).symm) (chartAt E p p) := by
  have hmat (y : E) : metricCoefficients g p y =
      bilinearCoordinateMatrix (Module.finBasis ℝ E) (chartMetricForm g p y) := by
    ext i j
    rw [bilinearCoordinateMatrix,chartMetricForm_pairing]
    rfl
  have hs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (chartAt E p).symm := by
    have h := contMDiffOn_chart_symm (I:=𝓘(ℝ,E)) (n:=∞) (x:=p)
    rwa [ht,contMDiffOn_univ] at h
  have hT : Differentiable ℝ (chartMetricForm g p) := by
    have h := chartMetricForm_contDiffOn g p
    rw [ht,contDiffOn_univ] at h
    exact h.differentiable (by simp)
  change coordinateMetricLaplacian (Module.finBasis ℝ E) (metricCoefficients g p)
    (u ∘ (chartAt E p).symm) (chartAt E p p) = _
  rw [show metricCoefficients g p = (fun y => bilinearCoordinateMatrix (Module.finBasis ℝ E) (chartMetricForm g p y)) from funext hmat]
  apply coordinateMetricLaplacian_change_basis_normed _ _ _ hT
    (chartMetricForm_symm g p) (fun y v hv => chartMetricForm_pos g p (ht ▸ mem_univ y) hv)
  exact ((contMDiff_iff_contDiff.mp (hu.comp hs)).of_le (show (2:WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2, u_4} : type_of% @OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ_oai.{u_1, u_2, u_4} := @OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ_oai.{u_1, u_2, u_4}
