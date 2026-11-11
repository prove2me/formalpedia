-- Prove2me | solution 1 for OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:24:59.223673+00:00
-- url     : https://prove2.me/submissions/2cc64caa-f791-45ba-9998-63018be94a4a

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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.LinearAlgebra.Matrix.Adjugate
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

lemma frameMap_axis (e : Fin 4 → _root_.OAI.Yau.Jets.Coord) (i : Fin 4) : frameMap e (Pi.single i 1) = e i := by
  simp [frameMap_apply, Pi.single_apply, ite_smul, eq_comm]

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

end

open Set Filter
open scoped ContDiff Topology

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

lemma sourceHessian_apply (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y u v : _root_.OAI.Yau.Jets.Coord) : sourceHessian g S y u v =
      fderiv ℝ (fderiv ℝ S) y u v - fderiv ℝ S y (metricConnection (g y) (fderiv ℝ g y) u v) := rfl

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AdmissibleDirectionTriple
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma frame_pair_coordinate (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (ho : ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) (v : _root_.OAI.Yau.Jets.Coord) : g (e (Pi.single i 1)) v = e.symm v i := by
  calc
    _ = g (e (Pi.single i 1)) (e (e.symm v)) := by rw [e.apply_symm_apply]
    _ = _ := by
      have hexp : e.symm v = ∑ j : Fin 4, e.symm v j • Pi.single j (1:ℝ) := by
        ext j; simp [Pi.single_apply]
      conv_lhs => rw [hexp]
      simp [map_sum,map_smul,ho,smul_eq_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TripleWaveParameters
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
variable {g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {p : T → _root_.OAI.Yau.Jets.Coord}
namespace AdmissibleFrameTriple
variable (d : AdmissibleFrameTriple g H p)

lemma frame_orthonormal (z : T × Fin 3) (i j : Fin 4) :
    g z.1 (d.frame z (Pi.single i 1)) (d.frame z (Pi.single j 1)) = if i=j then 1 else 0 := by
  change g z.1 (frameMap (d.e z.1 z.2) (Pi.single i 1))
    (frameMap (d.e z.1 z.2) (Pi.single j 1)) = _
  simp only [frameMap_axis,d.orthonormal]

lemma frame_first (hpos : ∀ t v, v ≠ 0 → 0 < g t v v) (hp0 : ∀ t, p t ≠ 0)
    (z : T × Fin 3) : alpha (g := g) (p := p) z.1 • d.frame z (Pi.single 0 1) = p z.1 := by
  change alpha z.1 • frameMap (d.e z.1 z.2) (Pi.single 0 1) = _
  rw [frameMap_axis,d.first]
  simp [alpha,metricNormalize,smul_smul,ne_of_gt (Real.sqrt_pos.mpr (hpos z.1 _ (hp0 z.1)))]

lemma frame_second (hpos : ∀ t v, v ≠ 0 → 0 < g t v v) (hp0 : ∀ t, p t ≠ 0)
    (z : T × Fin 3) : beta (g := g) (p := p) z.1 • d.frame z (Pi.single 1 1) = d.q z.1 z.2 := by
  have hb : 0 < g z.1 (p z.1) (p z.1)+4 := by have h := hpos z.1 _ (hp0 z.1); linarith
  change beta z.1 • frameMap (d.e z.1 z.2) (Pi.single 1 1) = _
  rw [frameMap_axis,d.second]
  simp [beta,metricNormalize,d.length,smul_smul,ne_of_gt (Real.sqrt_pos.mpr hb)]
end AdmissibleFrameTriple

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ContactGeometry
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma scalar_chart_covariant_diagonal
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) :
    iteratedFDeriv ℝ 2 (f ∘ actualMetricChart g y e) 0 (fun _ ↦ v) =
      sourceHessian g f y (e v) (e v) := by
  rw [iteratedFDeriv_two_apply]
  rw [← directional_second (f ∘ actualMetricChart g y e) (hf.comp (quadraticChartMap_smooth _ _ _)) 0 v v]
  rw [show (actualMetricChart g y e : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = quadraticChartMap y e (actualFrameConnection g y e) from rfl]
  rw [scalar_chart_hessian f hf y e _
    (fun u v ↦ actual_connection_symmetric g hg hs hp y (e u) (e v))]
  rfl

lemma orthonormal_frame_norm_sq (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (ho : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) (v : _root_.OAI.Yau.Jets.Coord) :
    g (e v) (e v) = ∑ i, (v i)^2 := by
  have hv : e v = ∑ i, v i • e (Pi.single i 1) := by
    conv_lhs => rw [coord_expansion v]
    simp
  conv_lhs => arg 1; rw [hv]
  simp only [map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul]
  simp_rw [frame_pair_coordinate g e ho,e.symm_apply_apply,pow_two]

lemma source_eta_of_adapted_frame
    (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (ho : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (p q : _root_.OAI.Yau.Jets.Coord) (a b : ℝ) (ha : a • e (Pi.single 0 1) = p) (hb : b • e (Pi.single 1 1) = q) :
    Yau.contactEta a b (H (e (Pi.single 0 1)) (e (Pi.single 0 1)))
      (H (e (Pi.single 1 1)) (e (Pi.single 1 1))) = sourceDirectionEta g H p q := by
  rw [← ha,← hb]
  simp only [Yau.contactEta,sourceDirectionEta,map_smul,smul_apply,smul_eq_mul,ho,ite_true, if_true,mul_one]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    sourceHessian g S =ᶠ[𝓝 x] sourceHessian G A := by
  filter_upwards [hg,hg.fderiv (𝕜 := ℝ),hS.fderiv (𝕜 := ℝ),
    (hS.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)] with z hz hd hs hss
  simp only [sourceHessian,hz,hd,hs,hss]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CommonLocalExtension
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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem common_local_smooth_extension {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) {y : _root_.OAI.Yau.Jets.Coord} (hy : y ∈ U) :
    ∃ (r : ℝ) (G : _root_.OAI.Yau.Jets.Coord → F), 0 < r ∧ ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ U ∧ Metric.closedBall y r ⊆ U ∧
      (∀ x ∈ Metric.ball y r, G x = f x) ∧
      ∀ x ∈ Metric.ball y r, G =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let beta : ContDiffBump y := ⟨r/4, r/2, by positivity, by linarith⟩
  have hsupport : tsupport beta ⊆ U := by
    rw [beta.tsupport_eq]
    intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    dsimp [beta] at hx'
    linarith
  let G := fun x ↦ beta x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport beta
    · exact beta.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsupport hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with z hz
      simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hsub : tsupport G ⊆ tsupport beta := by
    apply closure_mono
    intro x hx
    change beta x ≠ 0
    intro hz
    exact hx (by simp [G, hz])
  have heq : ∀ x ∈ Metric.ball y (r/4), G x = f x := by
    intro x hx
    have hb : beta x = 1 := beta.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [G, hb]
  refine ⟨r/4, G, by positivity, hG,
    beta.hasCompactSupport.of_isClosed_subset isClosed_closure hsub,
    hsub.trans hsupport, ?_, heq, ?_⟩
  · intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    linarith
  · intro x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact heq z hz

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveCenterJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma zero_mem_source (t : T × Fin 3) : (0:_root_.OAI.Yau.Jets.Coord) ∈ (b.F t).source := by
  rw [(b.chart_domain t).1]
  simpa using b.sourceRadius_pos

lemma chart_zero (t : T × Fin 3) : b.F t 0 = y t.1 := by
  rw [b.chart_eq]
  exact quadraticChartMap_zero _ _ _

lemma center_mem_target (t : T × Fin 3) : y t.1 ∈ (b.F t).target := by
  rw [← b.chart_zero t]
  exact (b.F t).map_source (b.zero_mem_source t)

lemma inverse_center (t : T × Fin 3) : (b.F t).symm (y t.1) = 0 := by
  rw [← b.chart_zero t]
  exact (b.F t).left_inv (b.zero_mem_source t)

lemma inverse_derivative (t : T × Fin 3) :
    HasFDerivAt ((b.F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (d.frame t).symm.toContinuousLinearMap (y t.1) := by
  apply (b.F t).hasFDerivAt_symm (b.center_mem_target t)
  rw [b.inverse_center,b.chart_eq]
  exact quadraticChartMap_deriv_zero _ _ _

lemma phase_smooth_at_center (t : T × Fin 3) : ContDiffAt ℝ ∞ (b.phase t) (y t.1) :=
  (reval_contDiff _).contDiffAt.comp _ ((b.chart_domain t).2.2.contDiffAt
    ((b.F t).open_target.mem_nhds (b.center_mem_target t)))

lemma phase_first (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (b.phase t) (y t.1) v =
      (g (y t.1) (metricGradient g S (y t.1)) v:ℂ) +
        Complex.I * (g (y t.1) (d.q t.1 t.2) v:ℂ) := by
  have hder := ((reval_contDiff (b.phi t)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
  have he := (b.inverse_derivative t)
  have hf : fderiv ℝ (b.phase t) (y t.1) v =
      fderiv ℝ (reval (b.phi t)) 0 ((d.frame t).symm v) := by
    unfold phase
    rw [fderiv_comp _ (by rw [b.inverse_center]; exact hder.differentiableAt) he.differentiableAt,
      he.fderiv,b.inverse_center]
    rfl
  rw [hf,fderiv_reval]
  simp_rw [retained_phase_first _ _ _ _ (b.jets.phase_retained t 1 (by omega))]
  have hpair0 : g (y t.1) (metricGradient g S (y t.1)) v =
      sourceTripleAlpha g S y t * (d.frame t).symm v 0 := by
    have hframe : sourceTripleAlpha g S y t • d.frame t (Pi.single 0 1) = metricGradient g S (y t.1) :=
      d.frame_first (fun t ↦ hpos (y t)) hp0 t
    rw [← hframe]
    simp only [map_smul,smul_apply,smul_eq_mul]
    rw [frame_pair_coordinate (g (y t.1)) (d.frame t) (d.frame_orthonormal t)]
  have hpair1 : g (y t.1) (d.q t.1 t.2) v =
      sourceTripleBeta g S y t * (d.frame t).symm v 1 := by
    have hframe : sourceTripleBeta g S y t • d.frame t (Pi.single 1 1) = d.q t.1 t.2 :=
      d.frame_second (fun t ↦ hpos (y t)) hp0 t
    rw [← hframe]
    simp only [map_smul,smul_apply,smul_eq_mul]
    rw [frame_pair_coordinate (g (y t.1)) (d.frame t) (d.frame_orthonormal t)]
  rw [hpair0,hpair1]
  simp [normalFrameVector,Fin.sum_univ_succ]
  ring

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveSecondJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

omit [CompactSpace T] in
theorem phase_second
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (fun z ↦ (b.phase t z).re) (y t.1) v v =
      sourceHessian g S (y t.1) v v -
        sourceDirectionEta (g (y t.1)) (sourceHessian g S (y t.1))
          (metricGradient g S (y t.1)) (d.q t.1 t.2) * g (y t.1) v v := by
  let f : _root_.OAI.Yau.Jets.Coord → ℝ := fun z ↦ (b.phase t z).re
  have hf : ContDiffOn ℝ ∞ f (b.F t).target := by
    intro z hz
    exact (Complex.reCLM.contDiff.contDiffAt.comp z
      ((reval_contDiff _).contDiffAt.comp z
        ((b.chart_domain t).2.2.contDiffAt ((b.F t).open_target.mem_nhds hz)))).contDiffWithinAt
  obtain ⟨r,A,hr,hA,_,_,_,_,hAe⟩ := common_local_smooth_extension
    (b.F t).open_target f hf (b.center_mem_target t)
  have hAf : A =ᶠ[𝓝 (y t.1)] f := hAe _ (Metric.mem_ball_self hr)
  let Q : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord := actualMetricChart g (y t.1) (d.frame t)
  have hQ : ContDiff ℝ ∞ Q := quadraticChartMap_smooth _ _ _
  have hQ0 : Q 0 = y t.1 := quadraticChartMap_zero _ _ _
  have heF : (b.F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = Q := b.chart_eq t
  have hAQ : (A ∘ Q) =ᶠ[𝓝 (0:_root_.OAI.Yau.Jets.Coord)] (fun z ↦ (reval (b.phi t) z).re) := by
    have hmap : Tendsto Q (𝓝 0) (𝓝 (y t.1)) := by simpa only [ContinuousAt,hQ0] using (hQ.continuous.continuousAt (x := 0))
    filter_upwards [hAf.comp_tendsto hmap,(b.F t).open_source.mem_nhds (b.zero_mem_source t)] with z hz hzs
    change A (Q z) = _
    change A (Q z) = f (Q z) at hz
    rw [hz]
    change (reval (b.phi t) ((b.F t).symm (Q z))).re = _
    rw [← heF,(b.F t).left_inv hzs]
  have hHess : sourceHessian g A (y t.1) = sourceHessian g f (y t.1) :=
    (sourceHessian_eventuallyEq (Filter.EventuallyEq.refl (𝓝 (y t.1)) g) hAf).self_of_nhds
  let a := sourceTripleAlpha g S y t
  let bb := sourceTripleBeta g S y t
  let H := envelopeHessian (S ∘ Q)
  have ha : a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp (y t.1) (metricGradient g S (y t.1)) (hp0 t.1)))
  have hb : bb ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have hh := hp (y t.1) (metricGradient g S (y t.1)) (hp0 t.1)
    linarith
  have hSQ : ContDiff ℝ ∞ (S ∘ Q) := hS.comp hQ
  have hj := retained_normal_phase_derivatives (b.phi t) (S (y t.1)) a bb H ha hb
    (envelopeHessian_symmetric _ hSQ) (b.jets.phase_retained t)
  have heta : Yau.contactEta a bb (H 0 0) (H 1 1) =
      sourceDirectionEta (g (y t.1)) (sourceHessian g S (y t.1))
        (metricGradient g S (y t.1)) (d.q t.1 t.2) := by
    dsimp [H,Q]
    rw [charted_envelope_hessian g hg hs hp S hS,charted_envelope_hessian g hg hs hp S hS]
    exact source_eta_of_adapted_frame _ _ _ (d.frame_orthonormal t) _ _ a bb
      (d.frame_first (fun t ↦ hp (y t)) hp0 t) (d.frame_second (fun t ↦ hp (y t)) hp0 t)
  let u := (d.frame t).symm v
  have hsum : (∑ i, ∑ j, H i j*u i*u j) = sourceHessian g S (y t.1) v v := by
    rw [← envelopeHessian_diagonal]
    simpa only [u,Q,ContinuousLinearEquiv.apply_symm_apply] using
      scalar_chart_covariant_diagonal g hg hs hp S hS (y t.1) (d.frame t) u
  have hnorm : (∑ i, (u i)^2) = g (y t.1) v v := by
    simpa only [u,Q,ContinuousLinearEquiv.apply_symm_apply] using
      (orthonormal_frame_norm_sq (g (y t.1)) (d.frame t) (d.frame_orthonormal t) u).symm
  calc
    _ = sourceHessian g A (y t.1) v v := by rw [hHess]
    _ = iteratedFDeriv ℝ 2 (A ∘ Q) 0 (fun _ ↦ u) := by
      simpa only [u,Q,ContinuousLinearEquiv.apply_symm_apply] using
        (scalar_chart_covariant_diagonal g hg hs hp A hA (y t.1) (d.frame t) u).symm
    _ = iteratedFDeriv ℝ 2 (fun z ↦ (reval (b.phi t) z).re) 0 (fun _ ↦ u) := by
      rw [(hAQ.iteratedFDeriv ℝ 2).self_of_nhds]
    _ = (iteratedFDeriv ℝ 2 (reval (b.phi t)) 0 (fun _ ↦ u)).re := by
      exact congrArg (fun L : _root_.OAI.Yau.Jets.Coord [×2]→L[ℝ] ℝ ↦ L (fun _ ↦ u))
        (Complex.reCLM.iteratedFDeriv_comp_left (reval_contDiff _).contDiffAt
          (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
    _ = _ := by rw [hj.2.2 u,hsum,hnorm,heta]

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveHessian
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_symmetric_at
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hf : ContDiffAt ℝ ∞ f x) (u v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g f x u v = sourceHessian g f x v u := by
  simp only [sourceHessian_apply]
  rw [hf.isSymmSndFDerivAt
    (by simp) u v,
    actual_connection_symmetric g hg hs hp x u v]

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

omit [CompactSpace T] in
theorem phase_hessian
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (u v : _root_.OAI.Yau.Jets.Coord) :
    sourceHessian g (fun z ↦ (b.phase t z).re) (y t.1) u v =
      sourceHessian g S (y t.1) u v -
        sourceDirectionEta (g (y t.1)) (sourceHessian g S (y t.1))
          (metricGradient g S (y t.1)) (d.q t.1 t.2) * g (y t.1) u v := by
  have hu := b.phase_second hg hs hp hS hp0 t u
  have hv := b.phase_second hg hs hp hS hp0 t v
  have huv := b.phase_second hg hs hp hS hp0 t (u+v)
  have hsym := sourceHessian_symmetric_at g hg hs hp (fun z ↦ (b.phase t z).re) (y t.1)
    (Complex.reCLM.contDiff.contDiffAt.comp _ (b.phase_smooth_at_center t)) v u
  have hSsym := sourceHessian_symmetric_at g hg hs hp S (y t.1) hS.contDiffAt v u
  simp only [map_add,add_apply] at huv
  rw [hsym,hSsym,hs (y t.1) v u] at huv
  nlinarith

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPhaseJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma realPart_fderiv (f : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord) (hf : DifferentiableAt ℝ f x) (v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fun z ↦ (f z).re) x v = (fderiv ℝ f x v).re := by
  change fderiv ℝ (Complex.reCLM ∘ f) x v = _
  rw [(Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma real_phase_first (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fun z ↦ (b.phase t z).re) (y t.1) v = fderiv ℝ S (y t.1) v := by
  rw [realPart_fderiv _ _ ((b.phase_smooth_at_center t).differentiableAt (by simp)),
    b.phase_first hp hp0,metricGradient_pair g S _ (hp _) v]
  simp

lemma real_defect_second_oai (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) u v = -b.eta t*g (y t.1) u v := by
  have hphi : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) (y t.1) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (b.phase_smooth_at_center t)
  have hh := b.phase_hessian hg hs hp hS hp0 t u v
  simp only [sourceHessian_apply] at hh
  rw [b.real_phase_first hp hp0] at hh
  have hsub := iteratedFDeriv_sub_apply (i := 2)
    (hphi.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
    (hS.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
  have hv := congrArg (fun L : _root_.OAI.Yau.Jets.Coord [×2]→L[ℝ] ℝ ↦ L ![u,v]) hsub
  simp only [sub_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] at hv
  change fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) u v = _ at hv
  rw [hv]
  dsimp [eta]
  linarith

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second_oai.{u_1} := @OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second_oai.{u_1}
