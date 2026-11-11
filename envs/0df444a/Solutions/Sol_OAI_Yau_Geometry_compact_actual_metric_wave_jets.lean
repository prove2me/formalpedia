-- Prove2me | solution 1 for OAI.Yau.Geometry.compact_actual_metric_wave_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:25:00.473701+00:00
-- url     : https://prove2.me/submissions/92694287-4fa6-4c9f-98ab-520ce3d8153c

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_NormalOperatorFamily_solve_jets

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_QuadraticChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadraticChartMap_zero (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    quadraticChartMap y e B 0 = y := by simp [quadraticChartMap]

variable [CompleteSpace E]

lemma quadraticChart_coe (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    (quadraticChart y e B : E → E) = quadraticChartMap y e B := rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartMetric
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.Yau.Geometry.clmTopology
attribute [local instance] OAI.Yau.Geometry.clmAdd
attribute [local instance] OAI.Yau.Geometry.clmModule
lemma quadraticChartMap_fderiv (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (x : E) :
    fderiv ℝ (quadraticChartMap y e B) x = e.toContinuousLinearMap - B x := by
  rw [(quadraticChartMap_hasFDerivAt y e B x).fderiv]
  congr 1
  ext v
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.flip_apply]
  rw [hB v x]
  module

lemma quadraticChartMap_second (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (x : E) :
    HasFDerivAt (fderiv ℝ (quadraticChartMap y e B)) (-B) x := by
  have heq : fderiv ℝ (quadraticChartMap y e B) = fun z ↦ e.toContinuousLinearMap - B z :=
    funext (quadraticChartMap_fderiv y e B hB)
  rw [heq]
  convert (hasFDerivAt_const e.toContinuousLinearMap x).sub B.hasFDerivAt using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | simp only [zero_sub]

lemma pullbackMetric_quadratic_zero (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (u v : E) :
    pullbackMetric g (quadraticChartMap y e B) 0 u v = g y (e u) (e v) := by
  simp [pullbackMetric, quadraticChartMap_zero, (quadraticChartMap_deriv_zero y e B).fderiv]

lemma pullbackMetric_quadratic_hasFDerivAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (y : E)
    (hg : HasFDerivAt g D y) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (u v : E) :
    ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt (fun x ↦ pullbackMetric g (quadraticChartMap y e B) x u v) L 0 ∧
      ∀ w, L w = D (e w) (e u) (e v) -
        g y (B w u) (e v) - g y (e u) (B w v) := by
  let F := quadraticChartMap y e B
  have hF : HasFDerivAt F e.toContinuousLinearMap 0 := quadraticChartMap_deriv_zero y e B
  have hd := quadraticChartMap_second y e B hB (0:E)
  have hu := (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp 0 hd
  have hv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp 0 hd
  have hg' : HasFDerivAt g D (F 0) := by simpa [F, quadraticChartMap_zero] using hg
  have hgF := hg'.comp 0 hF
  have hp := (hgF.clm_apply hu).clm_apply hv
  refine ⟨_, hp, ?_⟩
  intro w
  simp [F, quadraticChartMap_zero, hF.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

theorem quadratic_chart_metric_first_zero (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (y : E)
    (hg : HasFDerivAt g D y) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u)
    (hcancel : ∀ w u v, D (e w) (e u) (e v) =
      g y (B w u) (e v) + g y (e u) (B w v)) (u v : E) :
    fderiv ℝ (fun x ↦ pullbackMetric g (quadraticChartMap y e B) x u v) 0 = 0 := by
  obtain ⟨L, hL, he⟩ := pullbackMetric_quadratic_hasFDerivAt g D y hg e B hB u v
  rw [hL.fderiv]
  ext w
  rw [he, hcancel]
  simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartHessianLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadraticChart_fderiv_apply_hasFDerivAt (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ u v, B u v = B v u) (x u : E) :
    HasFDerivAt (fun z ↦ fderiv ℝ (quadraticChartMap y e B) z u) (-(B.flip u)) x := by
  have h := (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp x
    (quadraticChartMap_second y e B hB x)
  convert h using 1 <;> rfl

lemma scalar_chart_first (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    fderiv ℝ (f ∘ quadraticChartMap y e B) 0 = (fderiv ℝ f y).comp e.toContinuousLinearMap := by
  have h := ((hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (x := y)).hasFDerivAt
  have h' : HasFDerivAt f (fderiv ℝ f y) (quadraticChartMap y e B 0) := by
    simpa [quadraticChartMap_zero] using h
  exact (h'.comp 0 (quadraticChartMap_deriv_zero y e B)).fderiv

theorem scalar_chart_hessian (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) (u v : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (f ∘ quadraticChartMap y e B) x u) 0 v =
      fderiv ℝ (fderiv ℝ f) y (e v) (e u) - fderiv ℝ f y (B v u) := by
  let F := quadraticChartMap y e B
  have hFs := quadraticChartMap_smooth y e B
  have heq : (fun x ↦ fderiv ℝ (f ∘ F) x u) =
      fun x ↦ fderiv ℝ f (F x) (fderiv ℝ F x u) := by
    funext x
    rw [fderiv_comp x ((hf.differentiable (by simp)) (F x))
      ((hFs.differentiable (by simp)) x)]
    rfl
  rw [heq]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) (F 0) := by
    simpa [F, quadraticChartMap_zero] using
      ((hdf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) y).hasFDerivAt
  have h := (hd.comp 0 (quadraticChartMap_deriv_zero y e B)).clm_apply
    (quadraticChart_fderiv_apply_hasFDerivAt y e B hB 0 u)
  convert congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h.fderiv using 1 <;>
    simp [F, quadraticChartMap_zero, (quadraticChartMap_deriv_zero y e B).fderiv]
  ring

end

attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma christoffelCovector_apply (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    christoffelCovector D u v w = (D u v w + D v u w - D w u v)/2 := by
  simp [christoffelCovector, ContinuousLinearMap.flip_apply]
  ring

lemma christoffelTensor_pair (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    m (christoffelTensor m D u v) w = (D u v w + D v u w - D w u v)/2 := by
  change m (m.symm (christoffelCovector D u v)) w = _
  rw [m.apply_symm_apply, christoffelCovector_apply]

lemma christoffelTensor_symmetric (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hD : ∀ w u v, D w u v = D w v u)
    (u v : E) : christoffelTensor m D u v = christoffelTensor m D v u := by
  apply m.injective
  ext w
  rw [christoffelTensor_pair, christoffelTensor_pair, hD w u v]
  ring

lemma christoffelTensor_cancel (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (hm : ∀ u v, m u v = m v u)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hD : ∀ w u v, D w u v = D w v u)
    (w u v : E) :
    D w u v = m (christoffelTensor m D w u) v + m u (christoffelTensor m D w v) := by
  rw [hm u (christoffelTensor m D w v), christoffelTensor_pair, christoffelTensor_pair]
  rw [hD w v u, hD u w v, hD v w u]
  ring

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricConnectionFamilyLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
lemma metricConnection_eq (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    metricConnection g D = christoffelTensor (positiveMetricEquiv g hp) D := by
  have hi : ContinuousLinearMap.inverse g = (positiveMetricEquiv g hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv g hp)
  simp only [metricConnection, christoffelTensor, hi]

variable {T : Type*} [TopologicalSpace T]
lemma positive_metric_inverse_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ ContinuousLinearMap.inverse (g t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g t) (hp t))).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g t) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact hc'.comp hg.continuousAt

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma christoffelCovector_continuous (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hD : Continuous D) : Continuous (fun t ↦ christoffelCovector (D t)) := by
  have hflip : Continuous (fun t ↦ (D t).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.comp hD
  exact ((hD.add hflip).sub (hflip.const_clm_comp
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).const_smul (1/2:ℝ)

theorem metricConnection_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ)
    (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g) (hD : Continuous D)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ metricConnection (g t) (D t)) := by
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.comp
    (positive_metric_inverse_continuous g hg hp)).clm_comp (christoffelCovector_continuous D hD)

theorem smooth_metric_connection_continuous (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y, ∀ v : E, v ≠ 0 → 0 < g y v v) :
    Continuous (fun y ↦ metricConnection (g y) (fderiv ℝ g y)) := by
  exact metricConnection_continuous g (fderiv ℝ g) hg.continuous
    (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hp

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma metric_derivative_symmetric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (y : E) (hg : HasFDerivAt g D y)
    (hs : ∀ x u v, g x u v = g x v u) : ∀ w u v, D w u v = D w v u := by
  intro w u v
  have huv := (hg.clm_apply (hasFDerivAt_const u y)).clm_apply (hasFDerivAt_const v y)
  have hvu := (hg.clm_apply (hasFDerivAt_const v y)).clm_apply (hasFDerivAt_const u y)
  have he : (fun x ↦ g x u v) = fun x ↦ g x v u := funext (fun x ↦ hs x u v)
  have hh := congrArg (fun f : E → ℝ ↦ fderiv ℝ f y w) he
  rw [huv.fderiv, hvu.fderiv] at hh
  simpa using hh

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_JetCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

lemma homogeneousComponent_pderiv (p : CPoly) (n : ℕ) (i : Fin 4) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n + 1) p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single]
  by_cases hd : d.degree = n
  · simp [hd]
  · simp [hd]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialEvaluation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma reval_contDiff (p : CPoly) : ContDiff ℝ ∞ (reval p) := by
  change ContDiff ℝ ∞ (fun x ↦ reval p x)
  induction p using MvPolynomial.induction_on with
  | C a => simpa [reval] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Coord ↦ a))
  | add p q hp hq => simpa [reval] using hp.add hq
  | mul_X p i hp =>
    simpa [reval, coordCLM] using hp.mul (coordCLM i).contDiff

theorem fderiv_reval (p : CPoly) (x v : Coord) :
    fderiv ℝ (reval p) x v = ∑ i, reval (pderiv i p) x * (v i : ℂ) := by
  have hd (p : CPoly) : DifferentiableAt ℝ (reval p) x :=
    (reval_contDiff p).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : reval (C a) = fun _ ↦ a := by ext; simp [reval]
    rw [he]
    simp [reval]
  | add p q hp hq =>
    have he : reval (p + q) = fun x ↦ reval p x + reval q x := by ext; simp [reval]
    rw [he]
    change (fderiv ℝ (reval p + reval q) x) v = _
    rw [fderiv_add (hd p) (hd q)]
    simp only [add_apply, hp, hq, map_add, reval, add_mul,
      Finset.sum_add_distrib]
  | mul_X p j hp =>
    have he : reval (p * X j) = fun x ↦ reval p x * coordCLM j x := by
      ext; simp [reval, coordCLM]
    rw [he]
    change (fderiv ℝ (reval p * ⇑(coordCLM j)) x) v = _
    rw [fderiv_mul (hd p) (coordCLM j).differentiableAt]
    simp [hp, reval, coordCLM, pderiv_X, Finset.sum_add_distrib,
      Finset.mul_sum, mul_add, mul_comm, mul_left_comm, Pi.single_apply, apply_ite]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FrameMapFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {T : Type*} [TopologicalSpace T]

lemma frameConnection_continuous (B : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hB : Continuous B)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ frameConnection (B t) (e t)) := by
  exact (((ContinuousLinearMap.compL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord).flip.continuous.comp he).clm_comp hB).clm_comp he

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SpatialJetFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_spatial_fderiv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun z : P × E ↦ fderiv ℝ (f z.1) z.2) := by
  have h : ContDiff ℝ ∞ (fun z : (P × E) × E ↦ f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

theorem smooth_spatial_iteratedFDeriv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ContDiff ℝ ∞ (fun z : P × E ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hf
  | succ k ih =>
    have h := smooth_spatial_fderiv (fun p x ↦ iteratedFDeriv ℝ k (f p) x) ih
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F).symm.contDiff.comp h

variable {T : Type*} [TopologicalSpace T]

theorem continuous_spatial_jets_of_smooth_family (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (p : T → P) (hp : Continuous p) (k : ℕ) :
    Continuous (fun z : T × E ↦ iteratedFDeriv ℝ k (f (p z.1)) z.2) :=
  (smooth_spatial_iteratedFDeriv f hf k).continuous.comp
    ((hp.comp continuous_fst).prodMk continuous_snd)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_QuadraticFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma rawQuadratic_smooth :
    ContDiff ℝ ∞ (Function.uncurry (rawQuadratic (E := E))) := by
  exact (contDiff_fst.fst.add (contDiff_fst.snd.fst.clm_apply contDiff_snd)).sub
    ((contDiff_fst.snd.snd.clm_apply contDiff_snd).clm_apply contDiff_snd |>.const_smul (1/2:ℝ))

lemma pulledForm_smooth (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (Function.uncurry (pulledForm g)) := by
  let J : QuadParam E × E → E →L[ℝ] E := fun z ↦ fderiv ℝ (rawQuadratic z.1) z.2
  have hJ : ContDiff ℝ ∞ J :=
    smooth_spatial_fderiv (rawQuadratic (E := E)) rawQuadratic_smooth
  have hG : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦ g (rawQuadratic z.1 z.2)) :=
    hg.comp rawQuadratic_smooth
  let L : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E E ℝ).flip
  have hL₀ : ContDiff ℝ ∞ (fun A : E →L[ℝ] E ↦ L A) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E)
      (F := (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) L
  have hL : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦
      (ContinuousLinearMap.compL ℝ E E ℝ).flip (J z)) :=
    hL₀.comp hJ
  have hC : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦
      ((ContinuousLinearMap.compL ℝ E E ℝ).flip (J z)).comp (g (rawQuadratic z.1 z.2))) :=
    hL.clm_comp hG
  exact hC.clm_comp hJ

variable {T : Type*} [TopologicalSpace T]

theorem charted_scalar_spatial_jets (S : E → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B) (k : ℕ) :
    Continuous (fun z : T × E ↦ iteratedFDeriv ℝ k
      (S ∘ quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
  continuous_spatial_jets_of_smooth_family (fun p x ↦ S (rawQuadratic p x))
    (hS.comp rawQuadratic_smooth) (fun t ↦ (y t, (e t).toContinuousLinearMap, B t))
    (hy.prodMk (he.prodMk hB)) k

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdaptedChartFamilyLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Filter
open scoped ContDiff Topology
open Yau.Jets
attribute [local instance] clmTopology clmAdd clmModule

lemma actual_connection_symmetric (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (y u v : _root_.OAI.Yau.Jets.Coord) :
    metricConnection (g y) (fderiv ℝ g y) u v = metricConnection (g y) (fderiv ℝ g y) v u := by
  rw [metricConnection_eq (g y) (hp y)]
  exact christoffelTensor_symmetric _ _
    (metric_derivative_symmetric g _ y (hg.differentiable (by simp) y).hasFDerivAt hs) u v

lemma actual_connection_cancel (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (y w u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ g y w u v =
      g y (metricConnection (g y) (fderiv ℝ g y) w u) v +
      g y u (metricConnection (g y) (fderiv ℝ g y) w v) := by
  rw [metricConnection_eq (g y) (hp y)]
  exact christoffelTensor_cancel (positiveMetricEquiv (g y) (hp y)) (hs y) _
    (metric_derivative_symmetric g _ y (hg.differentiable (by simp) y).hasFDerivAt hs) w u v

lemma actualMetricChart_metric_first_zero (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fun x ↦ pullbackMetric g (actualMetricChart g y e) x u v) 0 = 0 := by
  exact quadratic_chart_metric_first_zero g _ y (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y).hasFDerivAt e _
    (fun u v ↦ actual_connection_symmetric g hg hs hp y (e u) (e v))
    (fun w u v ↦ actual_connection_cancel g hg hs hp y (e w) (e u) (e v)) u v

variable {T : Type*} [TopologicalSpace T]

lemma actualFrameConnection_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ actualFrameConnection g (y t) (e t)) :=
  frameConnection_continuous _ _ ((smooth_metric_connection_continuous g hg hp).comp hy) he

end

open Set Filter
open scoped ContDiff Topology
variable {T E F : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E]
  [TopologicalSpace F]

variable [NormedSpace ℝ E] [CompleteSpace E]

theorem compact_quadratic_chart_domain {s : Set T} (hs : IsCompact s)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B)
    {U : Set E} (hU : IsOpen U) (hyU : ∀ t ∈ s, y t ∈ U) :
    ∃ r > 0, ∀ t ∈ s, ∀ x : E, ‖x‖ < r →
      quadraticChartMap (y t) (e t) (B t) x ∈ U ∧
      ∃ J : E ≃L[ℝ] E, J.toContinuousLinearMap =
        fderiv ℝ (quadraticChartMap (y t) (e t) (B t)) x := by
  have hF : Continuous (fun z : T × E ↦ quadraticChartMap (y z.1) (e z.1) (B z.1) z.2) :=
    rawQuadratic_smooth.continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  have hJ : Continuous (fun z : T × E ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius hs _ hF hU
    (fun t ht ↦ by simpa [quadraticChartMap_zero] using hyU t ht)
  obtain ⟨d,hd,hdj⟩ := compact_family_common_radius hs _ hJ ContinuousLinearEquiv.isOpen
    (fun t _ ↦ ⟨e t, (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv.symm⟩)
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro t ht x hx
  exact ⟨hri t ht x (lt_of_lt_of_le hx (min_le_left _ _)),
    hdj t ht x (lt_of_lt_of_le hx (min_le_right _ _))⟩

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

theorem contactEta_pos {a b h00 h11 : ℝ} (ha : a ≠ 0)
    (h : 0 < a ^ 2 * h00 + b ^ 2 * h11) :
    0 < contactEta a b h00 h11 := by
  unfold contactEta
  apply div_pos h
  have := sq_pos_of_ne_zero ha
  positivity

theorem contactEta_compatibility {a b h00 h11 : ℝ} (ha : a ≠ 0) :
    a ^ 2 * (h00 - contactEta a b h00 h11) +
      b ^ 2 * (h11 - contactEta a b h00 h11) = 0 := by
  have hd : a ^ 2 + b ^ 2 ≠ 0 := by
    have := sq_pos_of_ne_zero ha
    positivity
  unfold contactEta
  field_simp
  ring

theorem imaginaryHessian_symmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {H : Matrix (Fin 4) (Fin 4) ℝ}
    (hc : a ^ 2 * H 0 0 + b ^ 2 * H 1 1 = 0) :
    ∀ i j, imaginaryHessian a b H i j = imaginaryHessian a b H j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [imaginaryHessian]
  all_goals field_simp
  all_goals nlinarith [hc]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformPolynomial
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T ι : Type*} [TopologicalSpace T] [Fintype ι]

omit [TopologicalSpace T] in
lemma polynomialFamily_iteratedFDeriv (p : ι → CPoly) (c : T → ι → ℂ) (t : T)
    (k : ℕ) (x : Coord) :
    iteratedFDeriv ℝ k (polynomialFamily p c t) x =
      ∑ i, c t i • iteratedFDeriv ℝ k (reval (p i)) x := by
  unfold polynomialFamily
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    (((reval_contDiff (p i)).const_smul (c t i)).of_le
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedFDeriv_const_smul_apply'
    ((reval_contDiff (p i)).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem polynomialFamily_derivative_continuous (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (k : ℕ) :
    Continuous (fun tx : T × Coord ↦ iteratedFDeriv ℝ k (polynomialFamily p c tx.1) tx.2) := by
  simp_rw [polynomialFamily_iteratedFDeriv]
  apply continuous_finsetSum
  intro i _
  exact ((hc i).comp continuous_fst).smul
    (((reval_contDiff (p i)).continuous_iteratedFDeriv (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).comp continuous_snd)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ContinuousPolynomialFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma polynomial_sum_of_support_subset (p : CPoly) (s : Finset (Fin 4 →₀ ℕ))
    (hs : p.support ⊆ s) : p = ∑ d ∈ s, p.coeff d • monomial d (1 : ℂ) := by
  simp only [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [p.as_sum]
  exact Finset.sum_subset hs (fun d _ hd ↦ by simp [notMem_support_iff.mp hd])

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_InitialPhasePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma pderiv_linearPhase (v : Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (linearPhase v) = C (v i) := by
  simp [linearPhase, pderiv_X, Pi.single_apply]

lemma pderiv_quadraticPhase (H : Fin 4 → Fin 4 → ℂ)
    (hH : ∀ i j, H i j = H j i) (i : Fin 4) :
    pderiv i (quadraticPhase H) = ∑ j, C (H i j) * X j := by
  simp only [quadraticPhase, pderiv_mul, map_sum, pderiv_C, pderiv_X, Pi.single_apply,
    zero_mul, zero_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  have he : (∑ j, C (H j i) * X j) = ∑ j, C (H i j) * X j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
  rw [he]
  have hs : (∑ x, ∑ j, if x = i then C (H x j) * X j else 0) =
      ∑ j, C (H i j) * X j := by
    rw [Finset.sum_comm]
    simp
  rw [hs, ← two_mul, ← mul_assoc]
  have hc : C (1/2 : ℂ) * (2:CPoly) = 1 := by
    calc
      _ = C ((1/2 : ℂ)*2) := by rw [map_mul]; congr 1
      _ = _ := by norm_num
  rw [hc, one_mul]

lemma pderiv_twice_quadraticPhase (H : Fin 4 → Fin 4 → ℂ)
    (hH : ∀ i j, H i j = H j i) (i j : Fin 4) :
    pderiv j (pderiv i (quadraticPhase H)) = C (H i j) := by
  rw [pderiv_quadraticPhase H hH]
  exact pderiv_linearPhase (H i) j

lemma initialPhaseJet_first (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (initialPhaseJet S v H 1) = C (v i) := by
  simpa [initialPhaseJet] using pderiv_linearPhase v i

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NormalFramePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma normalRealHessian_compatibility {a b : ℝ} (ha : a ≠ 0) (H : Fin 4 → Fin 4 → ℝ) :
    a^2 * normalRealHessian a b H 0 0 + b^2 * normalRealHessian a b H 1 1 = 0 := by
  simpa [normalRealHessian] using Yau.contactEta_compatibility (b := b) (h00 := H 0 0) (h11 := H 1 1) ha

lemma normalComplexHessian_symmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∀ i j, normalComplexHessian a b H i j = normalComplexHessian a b H j i := by
  intro i j
  have hK := Yau.imaginaryHessian_symmetric ha hb (normalRealHessian_compatibility ha H) i j
  have hR : normalRealHessian a b H i j = normalRealHessian a b H j i := by
    simp only [normalRealHessian, hH i j, eq_comm]
  simp only [normalComplexHessian, hK, hR]

lemma normalComplexHessian_real (a b : ℝ) (H : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) :
    (normalComplexHessian a b H i j).re =
      H i j - if i = j then Yau.contactEta a b (H 0 0) (H 1 1) else 0 := by
  simp [normalComplexHessian, normalRealHessian]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NormalFrameContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma contactEta_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) :
    Continuous (fun t ↦ Yau.contactEta (a t) (b t) (H t 0 0) (H t 1 1)) := by
  apply Continuous.div (((ha.pow 2).mul (hH 0 0)).add ((hb.pow 2).mul (hH 1 1)))
    ((ha.pow 2).add (hb.pow 2))
  intro t
  change a t ^ 2 + b t ^ 2 ≠ 0
  have h := sq_pos_of_ne_zero (ha0 t)
  nlinarith [sq_nonneg (b t)]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Waves
open Set Filter
open scoped Topology ContDiff
noncomputable section
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedDeriv_line {f : E → F} {n k : ℕ} (hf : ContDiff ℝ n f)
    (hk : k ≤ n) (y z : E) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ ↦ f (y + s • z)) t =
      iteratedFDeriv ℝ k f (y + t • z) (fun _ ↦ z) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight z
  have hshift : ContDiff ℝ n (fun x ↦ f (y + x)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k ((fun x ↦ f (y + x)) ∘ L) t (fun _ ↦ 1) = _
  rw [L.iteratedFDeriv_comp_right hshift t (by exact_mod_cast hk)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  simp [L]

theorem quadratic_gap_of_cubic_remainder {eta C r gap : ℝ}
    (hr : 0 ≤ r) (hsmall : C * r ≤ eta / 4)
    (hgap : gap ≤ -(eta / 2) * r ^ 2 + C * r ^ 3) :
    gap ≤ -(eta / 4) * r ^ 2 := by
  have := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hr hr)
  nlinarith

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ContactTaylor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Set Filter
open scoped Topology ContDiff
noncomputable section

lemma second_taylor_bound {f : Coord → ℝ} (hf : ContDiff ℝ ∞ f)
    (h0 : f 0 = 0) (h1 : fderiv ℝ f 0 = 0) (x : Coord) (C : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 3 f (t • x)‖ ≤ C) :
    f x ≤ (1/2:ℝ) * iteratedFDeriv ℝ 2 f 0 (fun _ ↦ x) + C * ‖x‖^3 / 2 := by
  let g : ℝ → ℝ := fun t ↦ f (t • x)
  have hgf : ContDiff ℝ (3:ℕ) g :=
    (hf.of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top)).comp
      (contDiff_id.smul contDiff_const)
  have hi (k : ℕ) (hk : k ≤ 3) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      iteratedDerivWithin k g (Icc (0:ℝ) 1) t =
        iteratedFDeriv ℝ k f (t • x) (fun _ ↦ x) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1))
      (hgf.of_le (by exact_mod_cast hk)).contDiffAt ht]
    simpa [g] using Yau.Waves.iteratedDeriv_line
      (hf.of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top)) hk (0:Coord) x t
  have htaylor : taylorWithinEval g 2 (Icc (0:ℝ) 1) 0 1 =
      (1/2:ℝ) * iteratedFDeriv ℝ 2 f 0 (fun _ ↦ x) := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hi 0 (by omega) 0 (by constructor <;> norm_num),
      hi 1 (by omega) 0 (by constructor <;> norm_num),
      hi 2 (by omega) 0 (by constructor <;> norm_num)]
    simp [h0, h1, iteratedFDeriv_one_apply]
  have hderiv : ∀ t ∈ Icc (0:ℝ) 1,
      ‖iteratedDerivWithin 3 g (Icc (0:ℝ) 1) t‖ ≤ C * ‖x‖^3 := by
    intro t ht
    rw [hi 3 le_rfl t ht]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hb t ht) (pow_nonneg (norm_nonneg x) 3))
  have h := taylor_mean_remainder_bound (by norm_num : (0:ℝ) ≤ 1)
    hgf.contDiffOn (by constructor <;> norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1) hderiv
  rw [htaylor] at h
  norm_num [g] at h
  have hh := (le_abs_self (f x - (1/2:ℝ) * iteratedFDeriv ℝ 2 f 0 (fun _ ↦ x))).trans h
  linarith

variable {T : Type*} [TopologicalSpace T]

theorem uniform_contact_from_second_jet {s : Set T} (hs : IsCompact s)
    (f : T → Coord → ℝ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hc : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ 3 (f z.1) z.2))
    (eta : T → ℝ) (heta : ContinuousOn eta s) (hpos : ∀ t ∈ s, 0 < eta t)
    (h0 : ∀ t ∈ s, f t 0 = 0) (h1 : ∀ t ∈ s, fderiv ℝ (f t) 0 = 0)
    (h2 : ∀ t ∈ s, ∀ x : Coord,
      iteratedFDeriv ℝ 2 (f t) 0 (fun _ ↦ x) ≤ -eta t * ‖x‖^2) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) → f t x ≤ -c*‖x‖^2 := by
  obtain ⟨e, he, _, _, heB⟩ := compact_positive_bounds hs eta heta hpos
  obtain ⟨C, hC, hb⟩ := ((hs.prod (isCompact_closedBall (0:Coord) 1)).image hc).isBounded.exists_pos_norm_le
  have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div, mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
  have hsmall := ht.eventually (eventually_lt_nhds (lt_min (by norm_num : (0:ℝ) < 1)
    (div_pos he (mul_pos (by norm_num : (0:ℝ)<4) hC))))
  refine ⟨e/4, by positivity, ?_⟩
  filter_upwards [hsmall] with N hN
  intro t hts x hx
  have hx1 : ‖x‖ ≤ 1 := hx.trans (le_of_lt (lt_of_lt_of_le hN (min_le_left _ _)))
  have hxC : C * ‖x‖ ≤ e / 4 := by
    have hh := hx.trans (le_of_lt (lt_of_lt_of_le hN (min_le_right _ _)))
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hC)).mp hh
    nlinarith
  have hseg : ∀ r ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 3 (f t) (r • x)‖ ≤ C := by
    intro r hr
    apply hb _
    refine ⟨(t,r • x), ⟨hts, ?_⟩, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hr.2 (norm_nonneg x)).trans (by simpa using hx1)
  have htay := second_taylor_bound (hf t) (h0 t hts) (h1 t hts) x C hseg
  have htwo := h2 t hts x
  have heta' := mul_le_mul_of_nonneg_right (heB t hts).1 (sq_nonneg ‖x‖)
  apply Yau.Waves.quadratic_gap_of_cubic_remainder (norm_nonneg x) hxC
  nlinarith [mul_nonneg hC.le (pow_nonneg (norm_nonneg x) 3)]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseActualJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma reval_zero_homogeneous (p : CPoly) :
    reval p 0 = reval (homogeneousComponent 0 p) 0 := by
  simp [reval, constantCoeff_eq]

lemma retained_phase_value (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ)
    (h : homogeneousComponent 0 p = initialPhaseJet s v H 0) : reval p 0 = (s:ℂ) := by
  rw [reval_zero_homogeneous, h]
  simp [initialPhaseJet, reval]

lemma retained_phase_first (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ)
    (h : homogeneousComponent 1 p = initialPhaseJet s v H 1) (i : Fin 4) :
    reval (pderiv i p) 0 = v i := by
  rw [reval_zero_homogeneous, homogeneousComponent_pderiv, show 0+1=1 from rfl, h,
    initialPhaseJet_first]
  simp [reval]

lemma retained_phase_second (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ) (hH : ∀ i j, H i j = H j i)
    (h : homogeneousComponent 2 p = initialPhaseJet s v H 2) (i j : Fin 4) :
    reval (pderiv j (pderiv i p)) 0 = H i j := by
  rw [reval_zero_homogeneous, homogeneousComponent_pderiv, homogeneousComponent_pderiv]
  rw [show 0+1+1=2 from rfl, h]
  simp only [initialPhaseJet, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega,
    ite_false, if_false, ite_true, if_true, pderiv_twice_quadraticPhase H hH]
  simp [reval]

lemma iteratedFDeriv_two_reval (p : CPoly) (x u v : Coord) :
    iteratedFDeriv ℝ 2 (reval p) x ![u,v] =
      ∑ i, ∑ j, reval (pderiv j (pderiv i p)) x * (v i:ℂ) * (u j:ℂ) := by
  have hd := (reval_contDiff p).contDiffAt.differentiableAt_iteratedFDeriv
    (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1:ℕ∞ω) < ∞) (x := x)
  rw [hd.iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, Fin.tail, Matrix.cons_val_succ]
  have he : (fun y ↦ fderiv ℝ (reval p) y v) =
      fun y ↦ ∑ i, reval (pderiv i p) y * (v i:ℂ) := by
    funext y
    exact fderiv_reval p y v
  rw [he, fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_mul_const]
    simp only [smul_apply, smul_eq_mul, fderiv_reval, Finset.mul_sum]
    simp [mul_comm, mul_left_comm]
    · exact (reval_contDiff _).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  · intro i _
    exact ((reval_contDiff _).mul contDiff_const).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x

theorem retained_normal_phase_derivatives (p : CPoly) (s a b : ℝ)
    (H : Fin 4 → Fin 4 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hH : ∀ i j, H i j = H j i)
    (hkeep : ∀ k, k ≤ 2 → homogeneousComponent k p =
      initialPhaseJet s (normalFrameVector a b) (normalComplexHessian a b H) k) :
    (reval p 0).re = s ∧
    (∀ x : Coord, (fderiv ℝ (reval p) 0 x).re = a*x 0) ∧
    ∀ x : Coord, (iteratedFDeriv ℝ 2 (reval p) 0 (fun _ ↦ x)).re =
      (∑ i, ∑ j, H i j * x i * x j) -
        Yau.contactEta a b (H 0 0) (H 1 1) * ∑ i, (x i)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [retained_phase_value p s _ _ (hkeep 0 (by omega))]
    rfl
  · intro x
    rw [fderiv_reval]
    simp_rw [retained_phase_first p s _ _ (hkeep 1 (by omega))]
    simp [normalFrameVector, Fin.sum_univ_succ]
  · intro x
    have hx : (fun _ : Fin 2 ↦ x) = ![x,x] := by ext i; fin_cases i <;> rfl
    rw [hx, iteratedFDeriv_two_reval]
    simp_rw [retained_phase_second p s _ _ (normalComplexHessian_symmetric ha hb H hH)
      (hkeep 2 (by omega))]
    change Complex.reCLM (∑ i, ∑ j, normalComplexHessian a b H i j * (x i:ℂ) * (x j:ℂ)) = _
    simp only [map_sum]
    change (∑ i, ∑ j, (normalComplexHessian a b H i j * (x i:ℂ) * (x j:ℂ)).re) = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    simp_rw [normalComplexHessian_real, sub_mul, ite_mul, zero_mul]
    simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, pow_two]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeContactJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma coord_expansion (x : Coord) : x = ∑ i, x i • Pi.single i (1:ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

lemma envelopeHessian_symmetric (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) :
    ∀ i j, envelopeHessian S i j = envelopeHessian S j i := by
  intro i j
  exact hS.contDiffAt.isSymmSndFDerivAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _

lemma envelopeHessian_diagonal (S : Coord → ℝ) (x : Coord) :
    iteratedFDeriv ℝ 2 S 0 (fun _ ↦ x) = ∑ i, ∑ j, envelopeHessian S i j*x i*x j := by
  rw [iteratedFDeriv_two_apply]
  conv_lhs => arg 1; rw [coord_expansion x]
  conv_lhs => arg 2; rw [coord_expansion x]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum, envelopeHessian]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coord_norm_sq_le (x : Coord) : ‖x‖^2 ≤ ∑ i, (x i)^2 := by
  have hs : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hb : ‖x‖ ≤ Real.sqrt (∑ i, (x i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : (x i)^2 ≤ ∑ j, (x j)^2 := Finset.single_le_sum
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, (x i)^2), sq_abs (x i), abs_nonneg (x i)]
  nlinarith [Real.sq_sqrt hs, norm_nonneg x, Real.sqrt_nonneg (∑ i, (x i)^2)]

theorem retained_phase_envelope_contact (p : CPoly) (S : Coord → ℝ)
    (hS : ContDiff ℝ ∞ S) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfirst : ∀ x : Coord, fderiv ℝ S 0 x = a*x 0)
    (hkeep : ∀ k, k ≤ 2 → homogeneousComponent k p =
      initialPhaseJet (S 0) (normalFrameVector a b)
        (normalComplexHessian a b (envelopeHessian S)) k)
    (hstrict : 0 < a^2*envelopeHessian S 0 0+b^2*envelopeHessian S 1 1) :
    (reval p 0).re-S 0 = 0 ∧
    fderiv ℝ (fun x ↦ (reval p x).re-S x) 0 = 0 ∧
    ∀ x : Coord, iteratedFDeriv ℝ 2 (fun z ↦ (reval p z).re-S z) 0 (fun _ ↦ x) ≤
      -Yau.contactEta a b (envelopeHessian S 0 0) (envelopeHessian S 1 1)*‖x‖^2 := by
  obtain ⟨h0,h1,h2⟩ := retained_normal_phase_derivatives p (S 0) a b (envelopeHessian S)
    ha hb (envelopeHessian_symmetric S hS) hkeep
  have hR : ContDiff ℝ ∞ (fun x ↦ (reval p x).re) := Complex.reCLM.contDiff.comp (reval_contDiff p)
  refine ⟨by rw [h0, sub_self], ?_, ?_⟩
  · rw [fderiv_fun_sub (hR.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0) (hS.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0)]
    ext x
    have hc := Complex.reCLM.hasFDerivAt.comp 0 ((reval_contDiff p).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
    change fderiv ℝ (Complex.reCLM ∘ reval p) 0 x - fderiv ℝ S 0 x = 0
    rw [hc.fderiv]
    simp [h1 x, hfirst x]
  · intro x
    change iteratedFDeriv ℝ 2 ((fun z ↦ (reval p z).re) - S) 0 (fun _ ↦ x) ≤ _
    rw [iteratedFDeriv_sub_apply
      (hR.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (hS.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))]
    change iteratedFDeriv ℝ 2 (Complex.reCLM ∘ reval p) 0 (fun _ ↦ x) -
      iteratedFDeriv ℝ 2 S 0 (fun _ ↦ x) ≤ _
    rw [Complex.reCLM.iteratedFDeriv_comp_left (reval_contDiff p).contDiffAt
      (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top)]
    change (iteratedFDeriv ℝ 2 (reval p) 0 (fun _ ↦ x)).re - _ ≤ _
    rw [h2, envelopeHessian_diagonal]
    have he := Yau.contactEta_pos ha hstrict
    have hn := mul_le_mul_of_nonneg_left (coord_norm_sq_le x) he.le
    linarith

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_InverseMetricJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma form_derivative_zero (G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hG : DifferentiableAt ℝ G 0)
    (hz : ∀ u v, fderiv ℝ (fun x ↦ G x u v) 0 = 0) : fderiv ℝ G 0 = 0 := by
  ext w u v
  have hd := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const u 0)).clm_apply (hasFDerivAt_const v 0)
  have hh := congrArg (fun L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ ↦ L w) (hz u v)
  rw [hd.fderiv] at hh
  simpa using hh

lemma inverse_fderiv_zero
    (G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (he : G 0 = e.toContinuousLinearMap)
    (hG : DifferentiableAt ℝ G 0) (hz : fderiv ℝ G 0 = 0) :
    DifferentiableAt ℝ (fun x ↦ ContinuousLinearMap.inverse (G x)) 0 ∧
    fderiv ℝ (fun x ↦ ContinuousLinearMap.inverse (G x)) 0 = 0 := by
  have hi : DifferentiableAt ℝ
      (ContinuousLinearMap.inverse : (_root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) → ((_root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) →L[ℝ] _root_.OAI.Yau.Jets.Coord)) (G 0) := by
    rw [he]
    exact (contDiffAt_map_inverse (n := (1:ℕ∞ω)) e).differentiableAt (by norm_num)
  constructor
  · exact hi.comp (0:_root_.OAI.Yau.Jets.Coord) hG
  · change fderiv ℝ (ContinuousLinearMap.inverse ∘ G) 0 = 0
    rw [fderiv_comp (0:_root_.OAI.Yau.Jets.Coord) hi hG, hz, ContinuousLinearMap.comp_zero]

lemma orthonormal_inverse_axis (G : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < G v v)
    (he : ∀ i j : Fin 4, G (Pi.single i 1) (Pi.single j 1) = if i=j then 1 else 0)
    (j : Fin 4) : ContinuousLinearMap.inverse G (ContinuousLinearMap.proj j) = Pi.single j 1 := by
  have hi : ContinuousLinearMap.inverse G = (positiveMetricEquiv G hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv G hp)
  rw [hi]
  apply (positiveMetricEquiv G hp).injective
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  ext x
  have hx : G (Pi.single j 1) x = x j := by
    conv_lhs => arg 2; rw [coord_expansion x]
    simp [map_sum, he, mul_ite]
  exact hx.symm

lemma pulledForm_slice_smooth
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) (p : QuadParam _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (pulledForm g p) := by
  have hpair : ContDiff ℝ ∞ (fun x : _root_.OAI.Yau.Jets.Coord ↦ (p,x)) := contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def, Function.uncurry_def] using
    (pulledForm_smooth (E := _root_.OAI.Yau.Jets.Coord) g hg).comp hpair

theorem actual_inverse_metric_normal_jets
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) :
    (∀ i j, inverseChartCoeff g y e i j 0 = if i=j then 1 else 0) ∧
    ∀ i j, fderiv ℝ (inverseChartCoeff g y e i j) 0 = 0 := by
  let G := pulledForm g (y,e.toContinuousLinearMap,actualFrameConnection g y e)
  have hG : ContDiff ℝ ∞ G := pulledForm_slice_smooth g hg _
  have hv (u v : _root_.OAI.Yau.Jets.Coord) : G 0 u v = g y (e u) (e v) := pullbackMetric_quadratic_zero g y e _ u v
  have hpos : ∀ v, v ≠ 0 → 0 < G 0 v v := by
    intro v hv0
    rw [hv]
    exact hp y (e v) (by intro hz; exact hv0 (e.injective (by simpa using hz)))
  have hnormal : ∀ i j : Fin 4, G 0 (Pi.single i 1) (Pi.single j 1) = if i=j then 1 else 0 := by
    intro i j
    rw [hv]
    exact he i j
  have hz : fderiv ℝ G 0 = 0 := form_derivative_zero G (hG.differentiable (by simp) 0)
    (fun u v ↦ actualMetricChart_metric_first_zero g hg hs hp y e u v)
  obtain ⟨hi,hzi⟩ := inverse_fderiv_zero G (positiveMetricEquiv (G 0) hpos) rfl
    (hG.differentiable (by simp) 0) hz
  constructor
  · intro i j
    change (ContinuousLinearMap.inverse (G 0) (ContinuousLinearMap.proj j)) i = _
    rw [orthonormal_inverse_axis (G 0) hpos hnormal]
    simp [Pi.single_apply]
  · intro i j
    have h := (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).hasFDerivAt.comp (0:_root_.OAI.Yau.Jets.Coord)
      (hi.hasFDerivAt.clm_apply (hasFDerivAt_const (ContinuousLinearMap.proj j : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (0:_root_.OAI.Yau.Jets.Coord)))
    change fderiv ℝ ((ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) ∘
      (fun x ↦ ContinuousLinearMap.inverse (G x) (ContinuousLinearMap.proj j : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ))) 0 = 0
    rw [h.fderiv]
    simp only [hzi, ContinuousLinearMap.comp_zero, zero_add]
    ext v
    simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalSpatialJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_spatial_fderiv_at (f : P → E → F) (p : P) (x : E)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) :
    ContDiffAt ℝ ∞ (fun z : P × E ↦ fderiv ℝ (f z.1) z.2) (p,x) := by
  have h : ContDiffAt ℝ ∞ (fun z : (P × E) × E ↦ f z.1.1 z.2) ((p,x),x) := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (ContDiffAt.comp (g := Function.uncurry f)
        (f := fun z : (P × E) × E ↦ (z.1.1,z.2)) ((p,x),x) hf
        (contDiffAt_fst.fst.prodMk contDiffAt_snd))
  exact h.fderiv contDiffAt_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

lemma smooth_spatial_iteratedFDeriv_at (f : P → E → F) (p : P) (x : E)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z : P × E ↦ iteratedFDeriv ℝ k (f z.1) z.2) (p,x) := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.contDiffAt.comp (p,x) hf
  | succ k ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F).symm.contDiff.contDiffAt.comp
      (p,x) (smooth_spatial_fderiv_at (fun p x ↦ iteratedFDeriv ℝ k (f p) x) p x ih)

variable [CompleteSpace E]

theorem inversePulledForm_smooth_at (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : QuadParam E) (x : E)
    (m : E ≃L[ℝ] E →L[ℝ] ℝ) (hm : pulledForm g p x = m.toContinuousLinearMap) :
    ContDiffAt ℝ ∞ (Function.uncurry (inversePulledForm g)) (p,x) := by
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E))
      (pulledForm g p x) := by
    rw [hm]
    exact contDiffAt_map_inverse m
  exact hi.comp (p,x) (pulledForm_smooth g hg).contDiffAt

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TransformedDensity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma coordDet_smooth : ContDiff ℝ ∞ coordDet := by
  have hdet : coordDet = fun J : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord ↦
      ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, J (Pi.single i 1) (σ i) := by
    funext J
    exact Matrix.det_apply' _
  rw [hdet]
  apply ContDiff.sum
  intro sigma _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (ContinuousLinearMap.proj (sigma i) : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.comp
    (contDiff_id.clm_apply contDiff_const)

lemma coordDet_equiv_ne_zero (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : coordDet J.toContinuousLinearMap ≠ 0 := by
  change (LinearMap.toMatrix' J.toLinearEquiv.toLinearMap).det ≠ 0
  rw [LinearMap.det_toMatrix']
  exact J.toLinearEquiv.isUnit_det'.ne_zero

lemma chartDensity_pos (w : _root_.OAI.Yau.Jets.Coord → ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hw : 0 < w (rawQuadratic p x)) (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    0 < chartDensity w p x := by
  unfold chartDensity
  rw [hJ]
  exact mul_pos hw (abs_pos.mpr (coordDet_equiv_ne_zero J))

theorem chartDensity_smooth_at (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    ContDiffAt ℝ ∞ (Function.uncurry (chartDensity w)) (p,x) := by
  have hdet := coordDet_smooth.comp (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth)
  have hn : coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0 := by
    rw [hJ]; exact coordDet_equiv_ne_zero J
  exact (hw.comp rawQuadratic_smooth).contDiffAt.mul (hdet.contDiffAt.abs hn)

lemma pulledForm_positive (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    ∀ v, v ≠ 0 → 0 < pulledForm g p x v v := by
  intro v hv
  change 0 < g (rawQuadratic p x) (fderiv ℝ (rawQuadratic p) x v) (fderiv ℝ (rawQuadratic p) x v)
  rw [hJ]
  exact hp (J v) (by intro hz; exact hv (J.injective (by simpa using hz)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CommonCoefficientExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
variable {P E F T : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace T]

lemma cutoffCoefficient_smooth_at (beta : E → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (f : P → E → F) (p : P) (x : E)
    (hf : x ∈ tsupport beta → ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) :
    ContDiffAt ℝ ∞ (Function.uncurry (cutoffCoefficient beta f)) (p,x) := by
  by_cases hx : x ∈ tsupport beta
  · exact (hbeta.contDiffAt.comp (p,x) contDiffAt_snd).smul (hf hx)
  · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
    have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
    have hpair : ∀ᶠ z : P × E in 𝓝 (p,x), z.2 ∈ (tsupport beta)ᶜ :=
      continuousAt_snd.tendsto.eventually hn
    filter_upwards [hpair] with z hz
    simp [Function.uncurry_def, cutoffCoefficient, image_eq_zero_of_notMem_tsupport hz]

theorem common_cutoff_coefficient_family (beta : E → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (f : P → E → F) (p : T → P) (hp : Continuous p)
    (hf : ∀ t x, x ∈ tsupport beta → ContDiffAt ℝ ∞ (Function.uncurry f) (p t,x)) :
    (∀ t, ContDiff ℝ ∞ (cutoffCoefficient beta f (p t))) ∧
    ∀ k, Continuous (fun z : T × E ↦
      iteratedFDeriv ℝ k (cutoffCoefficient beta f (p z.1)) z.2) := by
  constructor
  · intro t
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (cutoffCoefficient_smooth_at beta hbeta f (p t) x (hf t x)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  · intro k
    apply continuous_iff_continuousAt.mpr
    rintro ⟨t,x⟩
    exact ContinuousAt.comp (x := (t,x))
      (g := fun z : P × E ↦ iteratedFDeriv ℝ k (cutoffCoefficient beta f z.1) z.2)
      (f := fun z : T × E ↦ (p z.1,z.2))
      (smooth_spatial_iteratedFDeriv_at (cutoffCoefficient beta f) (p t) x
        (cutoffCoefficient_smooth_at beta hbeta f (p t) x (hf t x)) k).continuousAt
      ((hp.comp continuous_fst).prodMk continuous_snd).continuousAt

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ E] in
lemma cutoffCoefficient_germ (beta : E → ℝ) (f : P → E → F) (p : P) (x : E)
    (hbeta : beta =ᶠ[𝓝 x] fun _ ↦ 1) : cutoffCoefficient beta f p =ᶠ[𝓝 x] f p := by
  filter_upwards [hbeta] with z hz
  simp [cutoffCoefficient, hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransformedDrift
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma chartPrincipal_smooth_at (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (Function.uncurry (chartPrincipal g i j)) (p,x) := by
  have hpos := pulledForm_positive g p x hp J hJ
  exact (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.contDiffAt.comp (p,x)
    ((inversePulledForm_smooth_at g hg p x
      (positiveMetricEquiv (pulledForm g p x) hpos) rfl).clm_apply contDiffAt_const)

lemma chartDrift_smooth_at (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v) (hwpos : 0 < w (rawQuadratic p x))
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (j : Fin 4) : ContDiffAt ℝ ∞ (Function.uncurry (chartDrift g w j)) (p,x) := by
  have hW := chartDensity_smooth_at w hw p x J hJ
  apply (hW.inv (ne_of_gt (chartDensity_pos w p x hwpos J hJ))).mul
  apply ContDiffAt.sum
  intro i _
  exact (smooth_spatial_fderiv_at (chartFlux g w i j) p x
    (hW.mul (chartPrincipal_smooth_at g hg p x hp J hJ i j))).clm_apply contDiffAt_const

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_ComplexChartCoefficient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {T : Type*} [TopologicalSpace T]

theorem complex_chart_coefficient_extensions
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : T → QuadParam _root_.OAI.Yau.Jets.Coord) (hp : Continuous p)
    (beta : _root_.OAI.Yau.Jets.Coord → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (hpos : ∀ t x, x ∈ tsupport beta → ∀ v, v ≠ 0 → 0 < g (rawQuadratic (p t) x) v v)
    (hwpos : ∀ t x, x ∈ tsupport beta → 0 < w (rawQuadratic (p t) x))
    (hJ : ∀ t x, x ∈ tsupport beta → ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap) :
    (∀ t i j, ContDiff ℝ ∞ (cutoffCoefficient beta (complexPrincipal g i j) (p t))) ∧
    (∀ t j, ContDiff ℝ ∞ (cutoffCoefficient beta (complexDrift g w j) (p t))) ∧
    (∀ k i j, Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k
      (cutoffCoefficient beta (complexPrincipal g i j) (p z.1)) z.2)) ∧
    ∀ k j, Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k
      (cutoffCoefficient beta (complexDrift g w j) (p z.1)) z.2) := by
  have hG (i j : Fin 4) := common_cutoff_coefficient_family beta hbeta (complexPrincipal g i j) p hp
    (fun t x hx ↦ by
      obtain ⟨J,hJe⟩ := hJ t x hx
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp (p t,x)
        (chartPrincipal_smooth_at g hg (p t) x (hpos t x hx) J hJe i j))
  have hB (j : Fin 4) := common_cutoff_coefficient_family beta hbeta (complexDrift g w j) p hp
    (fun t x hx ↦ by
      obtain ⟨J,hJe⟩ := hJ t x hx
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp (p t,x)
        (chartDrift_smooth_at g hg w hw (p t) x (hpos t x hx) (hwpos t x hx) J hJe j))
  exact ⟨fun t i j ↦ (hG i j).1 t, fun t j ↦ (hB j).1 t,
    fun k i j ↦ (hG i j).2 k, fun k j ↦ (hB j).2 k⟩

theorem extended_actual_metric_normal_jets
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (beta : _root_.OAI.Yau.Jets.Coord → ℝ) (hb : beta =ᶠ[𝓝 0] fun _ ↦ 1) :
    let p := (y,e.toContinuousLinearMap,actualFrameConnection g y e)
    (∀ i j, cutoffCoefficient beta (complexPrincipal g i j) p 0 = if i=j then 1 else 0) ∧
    ∀ i j, fderiv ℝ (cutoffCoefficient beta (complexPrincipal g i j) p) 0 = 0 := by
  dsimp only
  have hj := actual_inverse_metric_normal_jets g hg hs hp y e he
  constructor
  · intro i j
    rw [(cutoffCoefficient_germ beta (complexPrincipal g i j) _ 0 hb).self_of_nhds]
    change (inverseChartCoeff g y e i j 0 : ℂ) = _
    rw [hj.1 i j]
    split_ifs <;> simp
  · intro i j
    rw [(cutoffCoefficient_germ beta (complexPrincipal g i j) _ 0 hb).fderiv_eq]
    let p : QuadParam _root_.OAI.Yau.Jets.Coord := (y,e.toContinuousLinearMap,actualFrameConnection g y e)
    have hreal : ContDiffAt ℝ ∞ (inverseChartCoeff g y e i j) 0 := by
      have hJ : fderiv ℝ (rawQuadratic p) 0 = e.toContinuousLinearMap :=
        (quadraticChartMap_deriv_zero y e _).fderiv
      exact (chartPrincipal_smooth_at g hg p 0
        (by simpa [p, rawQuadratic] using hp y) e hJ i j).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    change fderiv ℝ (Complex.ofRealCLM ∘ inverseChartCoeff g y e i j) 0 = 0
    rw [(Complex.ofRealCLM.hasFDerivAt.comp 0 (hreal.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt).fderiv,
      hj.2 i j, ContinuousLinearMap.comp_zero]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartOperatorIdentity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma inverse_form_pair (G : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < G v v) (a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    G (ContinuousLinearMap.inverse G a) v = a v := by
  have hi : ContinuousLinearMap.inverse G = (positiveMetricEquiv G hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv G hp)
  change positiveMetricEquiv G hp (ContinuousLinearMap.inverse G a) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

lemma chartPrincipal_symmetric (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hs : ∀ x u v, g x u v = g x v u) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i j : Fin 4) : chartPrincipal g i j p x = chartPrincipal g j i p x := by
  have hpos := pulledForm_positive g p x hp J hJ
  have hsym (u v : _root_.OAI.Yau.Jets.Coord) : pulledForm g p x u v = pulledForm g p x v u := hs _ _ _
  have h := hsym (inversePulledForm g p x (ContinuousLinearMap.proj i))
    (inversePulledForm g p x (ContinuousLinearMap.proj j))
  change pulledForm g p x (ContinuousLinearMap.inverse (pulledForm g p x) (ContinuousLinearMap.proj i))
      (ContinuousLinearMap.inverse (pulledForm g p x) (ContinuousLinearMap.proj j)) = _ at h
  simp only [inversePulledForm] at h
  rw [inverse_form_pair _ hpos, inverse_form_pair _ hpos] at h
  exact h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseContactFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff Topology
open MvPolynomial Filter
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.spatial_derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (reval (P z.1)) z.2) := by
  obtain ⟨s, hs⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : s ↦ monomial d.val (1:ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach s (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i:ℂ)) (monomial d (1:ℂ)))).symm
  simp_rw [he]
  exact polynomialFamily_derivative_continuous
    (fun d : s ↦ monomial d.val (1:ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d : s ↦ hp.1 d.val) k

lemma ContinuousPolyFamily.real_spatial_derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (fun x ↦ (reval (P z.1) x).re) z.2) := by
  have he (t : T) (x : Coord) :
      iteratedFDeriv ℝ k (fun x ↦ (reval (P t) x).re) x =
        realTensorMap k (iteratedFDeriv ℝ k (reval (P t)) x) := by
    exact Complex.reCLM.iteratedFDeriv_comp_left (reval_contDiff _).contDiffAt
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
  simp_rw [he]
  exact (realTensorMap k).continuous.comp (hp.spatial_derivative_continuous k)

lemma phase_gap_spatial_derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (S : T → Coord → ℝ) (hS : ∀ t, ContDiff ℝ ∞ (S t))
    (hc : ∀ k, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (S z.1) z.2)) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (fun x ↦ (reval (P z.1) x).re-S z.1 x) z.2) := by
  have he (t : T) (x : Coord) :
      iteratedFDeriv ℝ k (fun x ↦ (reval (P t) x).re-S t x) x =
        iteratedFDeriv ℝ k (fun x ↦ (reval (P t) x).re) x - iteratedFDeriv ℝ k (S t) x := by
    exact iteratedFDeriv_sub_apply
      ((Complex.reCLM.contDiff.comp (reval_contDiff _)).contDiffAt.of_le
        (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)))
      ((hS t).contDiffAt.of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)))
  simp_rw [he]
  exact (hp.real_spatial_derivative_continuous k).sub (hc k)

theorem retained_phase_uniform_contact {s : Set T} (hs : IsCompact s)
    (P : T → CPoly) (hp : ContinuousPolyFamily P)
    (S : T → Coord → ℝ) (hS : ∀ t, ContDiff ℝ ∞ (S t))
    (hc : ∀ k, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (S z.1) z.2))
    (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0)
    (hHc : ∀ i j, Continuous (fun t ↦ envelopeHessian (S t) i j))
    (hfirst : ∀ t ∈ s, ∀ x : Coord, fderiv ℝ (S t) 0 x = a t*x 0)
    (hkeep : ∀ t ∈ s, ∀ k, k ≤ 2 → homogeneousComponent k (P t) =
      initialPhaseJet (S t 0) (normalFrameVector (a t) (b t))
        (normalComplexHessian (a t) (b t) (envelopeHessian (S t))) k)
    (hstrict : ∀ t ∈ s, 0 < (a t)^2*envelopeHessian (S t) 0 0+
      (b t)^2*envelopeHessian (S t) 1 1) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) → (reval (P t) x).re-S t x ≤ -c*‖x‖^2 := by
  have hj t ht := retained_phase_envelope_contact (P t) (S t) (hS t) (a t) (b t)
    (ha0 t) (hb0 t) (hfirst t ht) (hkeep t ht) (hstrict t ht)
  exact uniform_contact_from_second_jet hs (fun t x ↦ (reval (P t) x).re-S t x)
    (fun t ↦ (Complex.reCLM.contDiff.comp (reval_contDiff _)).sub (hS t))
    (phase_gap_spatial_derivative_continuous hp S hS hc 3)
    (fun t ↦ Yau.contactEta (a t) (b t) (envelopeHessian (S t) 0 0) (envelopeHessian (S t) 1 1))
    (contactEta_continuous a b _ ha hb hHc ha0).continuousOn
    (fun t ht ↦ Yau.contactEta_pos (ha0 t) (hstrict t ht))
    (fun t ht ↦ (hj t ht).1) (fun t ht ↦ (hj t ht).2.1) (fun t ht ↦ (hj t ht).2.2)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartedEnvelope
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_pair (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v) (v : _root_.OAI.Yau.Jets.Coord) :
    g y (metricGradient g S y) v = fderiv ℝ S y v := by
  have hi : ContinuousLinearMap.inverse (g y) = (positiveMetricEquiv (g y) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g y) hp)
  change positiveMetricEquiv (g y) hp (ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

lemma directional_second (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) (y u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fun x ↦ fderiv ℝ S x u) y v = fderiv ℝ (fderiv ℝ S) y v u := by
  rw [fderiv_clm_apply]
  · simp
  · exact ((hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
  · exact differentiableAt_const _

theorem charted_envelope_hessian
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (i j : Fin 4) :
    envelopeHessian (S ∘ actualMetricChart g y e) i j =
      sourceHessian g S y (e (Pi.single j 1)) (e (Pi.single i 1)) := by
  change fderiv ℝ (fderiv ℝ (S ∘ quadraticChartMap y e (actualFrameConnection g y e))) 0
    (Pi.single j 1) (Pi.single i 1) = _
  rw [← directional_second _ (hS.comp (quadraticChartMap_smooth _ _ _))]
  rw [scalar_chart_hessian S hS y e _
    (fun u v ↦ actual_connection_symmetric g hg hs hp y (e u) (e v))]
  rfl

lemma orthonormal_frame_pair (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0)
    (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : g (e (Pi.single i 1)) (e x) = x i := by
  have hx : e x = ∑ j, x j • e (Pi.single j 1) := by
    conv_lhs => rw [coord_expansion x]
    simp
  rw [hx]
  simp [map_sum, he, mul_ite]

theorem charted_envelope_adapted_data
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i = j then 1 else 0)
    (q : _root_.OAI.Yau.Jets.Coord) (a b : ℝ)
    (ha : a • e (Pi.single 0 1) = metricGradient g S y)
    (hb : b • e (Pi.single 1 1) = q)
    (hstrict : 0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
      sourceHessian g S y q q) :
    (∀ x : _root_.OAI.Yau.Jets.Coord, fderiv ℝ (S ∘ actualMetricChart g y e) 0 x = a*x 0) ∧
    0 < a^2*envelopeHessian (S ∘ actualMetricChart g y e) 0 0 +
      b^2*envelopeHessian (S ∘ actualMetricChart g y e) 1 1 := by
  constructor
  · intro x
    rw [show (actualMetricChart g y e : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) =
      quadraticChartMap y e (actualFrameConnection g y e) from rfl, scalar_chart_first S hS]
    change fderiv ℝ S y (e x) = _
    rw [← metricGradient_pair g S y (hp y) (e x), ← ha]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [orthonormal_frame_pair (g y) e he]
  · rw [charted_envelope_hessian g hg hs hp S hS, charted_envelope_hessian g hg hs hp S hS]
    rw [← ha, ← hb] at hstrict
    simp only [map_smul, smul_apply, smul_eq_mul] at hstrict
    nlinarith

variable {T : Type*} [TopologicalSpace T]

lemma envelopeHessian_family_continuous (S : T → _root_.OAI.Yau.Jets.Coord → ℝ)
    (hc : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ 2 (S z.1) z.2)) (i j : Fin 4) :
    Continuous (fun t ↦ envelopeHessian (S t) i j) := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ _root_.OAI.Yau.Jets.Coord) ℝ
    ![Pi.single j 1, Pi.single i 1]).continuous.comp (hc.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : T ↦ (0:_root_.OAI.Yau.Jets.Coord)))))
  simpa only [envelopeHessian, Function.comp_def, id_eq, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_GeometricContact
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff Topology
open Yau.Jets MvPolynomial Filter
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem actual_metric_chart_phase_contact {s : Set T} (hcompact : IsCompact s)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    (q : T → _root_.OAI.Yau.Jets.Coord) (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, b t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t ∈ s, 0 < sourceHessian g S (y t)
      (metricGradient g S (y t)) (metricGradient g S (y t)) + sourceHessian g S (y t) (q t) (q t))
    (P : T → CPoly) (hP : ContinuousPolyFamily P)
    (hkeep : ∀ t ∈ s, ∀ k, k ≤ 2 → homogeneousComponent k (P t) =
      initialPhaseJet (S (y t)) (normalFrameVector (a t) (b t))
        (normalComplexHessian (a t) (b t)
          (envelopeHessian (S ∘ actualMetricChart g (y t) (e t)))) k) :
    ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : _root_.OAI.Yau.Jets.Coord,
      ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (P t) x).re-S (actualMetricChart g (y t) (e t) x) ≤ -c*‖x‖^2 := by
  let S' : T → _root_.OAI.Yau.Jets.Coord → ℝ := fun t ↦ S ∘ actualMetricChart g (y t) (e t)
  have hS' (t : T) : ContDiff ℝ ∞ (S' t) := hS.comp (quadraticChartMap_smooth _ _ _)
  have hB := actualFrameConnection_continuous g hg hp y hy e he
  have hsc (k : ℕ) : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k (S' z.1) z.2) :=
    charted_scalar_spatial_jets S hS y hy e he _ hB k
  have hd t ht := charted_envelope_adapted_data g hg hs hp S hS (y t) (e t) (ho t)
    (q t) (a t) (b t) (hap t) (hbq t) (hstrict t ht)
  apply retained_phase_uniform_contact hcompact P hP S' hS' hsc a b ha hb ha0 hb0
    (envelopeHessian_family_continuous S' (hsc 2))
    (fun t ht ↦ (hd t ht).1) _ (fun t ht ↦ (hd t ht).2)
  intro t ht k hk
  simpa only [S', Function.comp_apply, actualMetricChart, quadraticChart_coe,
    quadraticChartMap_zero] using hkeep t ht k hk

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactNormalOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_actual_normal_operator
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x) :
    ∃ beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord),
      (∀ t x, x ∈ tsupport beta → rawQuadratic (metricChartParameter g (y t) (e t)) x ∈ U) ∧
      NormalOperatorFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta) := by
  have hB := actualFrameConnection_continuous g hg hpos y hy e he
  obtain ⟨r,hr,hri⟩ := compact_quadratic_chart_domain isCompact_univ y hy e he
    (fun t ↦ actualFrameConnection g (y t) (e t)) hB hU (fun t _ ↦ hyU t)
  let beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord) := ⟨r/4,r/2,by positivity,by linarith⟩
  have hnorm (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ tsupport beta) : ‖x‖ < r := by
    rw [beta.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at hx
    change ‖x‖ ≤ r/2 at hx
    linarith
  have hsource (t : T) (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ tsupport beta) :
      rawQuadratic (metricChartParameter g (y t) (e t)) x ∈ U :=
    (hri t (mem_univ t) x (hnorm x hx)).1
  have hp : Continuous (fun t ↦ metricChartParameter g (y t) (e t)) := hy.prodMk (he.prodMk hB)
  obtain ⟨hG,hb,hGc,hbc⟩ := complex_chart_coefficient_extensions g hg w hw
    (fun t ↦ metricChartParameter g (y t) (e t)) hp beta beta.contDiff
    (fun t x _ ↦ hpos _) (fun t x hx ↦ hwpos _ (hsource t x hx))
    (fun t x hx ↦ by
      obtain ⟨J,hJ⟩ := (hri t (mem_univ t) x (hnorm x hx)).2
      exact ⟨J,hJ.symm⟩)
  have hnormal (t : T) := extended_actual_metric_normal_jets g hg hs hpos (y t) (e t)
    (ho t) beta beta.eventuallyEq_one
  have hsym (t : T) (i j : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) :
      extendedPrincipal g y e beta t i j x = extendedPrincipal g y e beta t j i x := by
    by_cases hx : x ∈ tsupport beta
    · obtain ⟨J,hJ⟩ := (hri t (mem_univ t) x (hnorm x hx)).2
      have hh := chartPrincipal_symmetric g hs (metricChartParameter g (y t) (e t)) x
        (hpos _) J hJ.symm i j
      simp only [extendedPrincipal,cutoffCoefficient,complexPrincipal,hh]
    · simp [extendedPrincipal,cutoffCoefficient,image_eq_zero_of_notMem_tsupport hx]
  exact ⟨beta,hsource,⟨hG,hb,hGc,hbc,hsym,fun t ↦ (hnormal t).1,fun t ↦ (hnormal t).2⟩⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MetricWaveJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_actual_metric_wave_jets_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → _root_.OAI.Yau.Jets.Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (hm : 1 ≤ m) :
    ∃ (beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly),
      NormalOperatorFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta) ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
        (reval (phi t) x).re-S (actualMetricChart g (y t) (e t) x) ≤ -c*‖x‖^2 := by
  obtain ⟨beta,_,hG⟩ := compact_actual_normal_operator g hg hs hpos w hw y hy e he ho hU hyU hwpos
  have hconn := actualFrameConnection_continuous g hg hpos y hy e he
  have hSc (k : ℕ) : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k
      (S ∘ actualMetricChart g (y z.1) (e z.1)) z.2) :=
    charted_scalar_spatial_jets S hS y hy e he _ hconn k
  obtain ⟨phi,A,hjets⟩ := hG.solve_jets a bb (fun t ↦ S (y t))
    (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) ha hbb
    (hS.continuous.comp hy) (envelopeHessian_family_continuous _ (hSc 2)) ha0 hb0 hlen
    (fun t ↦ envelopeHessian_symmetric _ (hS.comp (quadraticChartMap_smooth _ _ _))) m J hm
  obtain ⟨c,hc,hgap⟩ := actual_metric_chart_phase_contact isCompact_univ g hg hs hpos S hS y hy e he ho
    q a bb ha hbb ha0 hb0 hap hbq (fun t _ ↦ hstrict t) phi hjets.phase_continuous
    (fun t _ ↦ hjets.phase_retained t)
  exact ⟨beta,phi,A,hG,hjets,c,hc,hgap.mono (fun _ h t ↦ h t (mem_univ t))⟩

end
end Yau.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Geometry.compact_actual_metric_wave_jets_oai.{u_1} := @OAI.Yau.Geometry.compact_actual_metric_wave_jets_oai.{u_1}
