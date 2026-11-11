-- Prove2me | solution 1 for OAI.Yau.Target.sphereChartTransition_divergence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:04.610732+00:00
-- url     : https://prove2.me/submissions/24106722-4116-48a4-8473-3488459c8860

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedCoordinateOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma coordPartial_mul_at (f u : Coord → ℂ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (i : Fin 4) :
    coordPartial i (fun z ↦ f z * u z) x =
      coordPartial i f x * u x + f x * coordPartial i u x := by
  unfold coordPartial
  rw [fderiv_fun_mul hf hu]
  simp [smul_eq_mul]
  ring

end
end Yau.Jets

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

lemma coordPartial_ofReal_at (f : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ (f z : ℂ)) x = (fderiv ℝ f x (Pi.single i 1) : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (Pi.single i 1) = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PiolaFour
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma adjugate_four_explicit (M : Fin 4 → Fin 4 → ℝ) :
    Matrix.adjugate M = !![(M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 + M 1 2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1), -(M 0 1 * M 2 2 * M 3 3 - M 0 1 * M 2 3 * M 3 2 - M 0 2 * M 2 1 * M 3 3 + M 0 2 * M 2 3 * M 3 1 + M 0 3 * M 2 1 * M 3 2 - M 0 3 * M 2 2 * M 3 1), (M 0 1 * M 1 2 * M 3 3 - M 0 1 * M 1 3 * M 3 2 - M 0 2 * M 1 1 * M 3 3 + M 0 2 * M 1 3 * M 3 1 + M 0 3 * M 1 1 * M 3 2 - M 0 3 * M 1 2 * M 3 1), -(M 0 1 * M 1 2 * M 2 3 - M 0 1 * M 1 3 * M 2 2 - M 0 2 * M 1 1 * M 2 3 + M 0 2 * M 1 3 * M 2 1 + M 0 3 * M 1 1 * M 2 2 - M 0 3 * M 1 2 * M 2 1);
      -(M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 - M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0), (M 0 0 * M 2 2 * M 3 3 - M 0 0 * M 2 3 * M 3 2 - M 0 2 * M 2 0 * M 3 3 + M 0 2 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 2 - M 0 3 * M 2 2 * M 3 0), -(M 0 0 * M 1 2 * M 3 3 - M 0 0 * M 1 3 * M 3 2 - M 0 2 * M 1 0 * M 3 3 + M 0 2 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 2 - M 0 3 * M 1 2 * M 3 0), (M 0 0 * M 1 2 * M 2 3 - M 0 0 * M 1 3 * M 2 2 - M 0 2 * M 1 0 * M 2 3 + M 0 2 * M 1 3 * M 2 0 + M 0 3 * M 1 0 * M 2 2 - M 0 3 * M 1 2 * M 2 0);
      (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1 - M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0), -(M 0 0 * M 2 1 * M 3 3 - M 0 0 * M 2 3 * M 3 1 - M 0 1 * M 2 0 * M 3 3 + M 0 1 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 1 - M 0 3 * M 2 1 * M 3 0), (M 0 0 * M 1 1 * M 3 3 - M 0 0 * M 1 3 * M 3 1 - M 0 1 * M 1 0 * M 3 3 + M 0 1 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 1 - M 0 3 * M 1 1 * M 3 0), -(M 0 0 * M 1 1 * M 2 3 - M 0 0 * M 1 3 * M 2 1 - M 0 1 * M 1 0 * M 2 3 + M 0 1 * M 1 3 * M 2 0 + M 0 3 * M 1 0 * M 2 1 - M 0 3 * M 1 1 * M 2 0);
      -(M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1 - M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0 + M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0), (M 0 0 * M 2 1 * M 3 2 - M 0 0 * M 2 2 * M 3 1 - M 0 1 * M 2 0 * M 3 2 + M 0 1 * M 2 2 * M 3 0 + M 0 2 * M 2 0 * M 3 1 - M 0 2 * M 2 1 * M 3 0), -(M 0 0 * M 1 1 * M 3 2 - M 0 0 * M 1 2 * M 3 1 - M 0 1 * M 1 0 * M 3 2 + M 0 1 * M 1 2 * M 3 0 + M 0 2 * M 1 0 * M 3 1 - M 0 2 * M 1 1 * M 3 0), (M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0)] := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix (n := 3) M i j, Matrix.det_fin_three]
  dsimp only [Matrix.submatrix]
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; all_goals first | (norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; done) | rfl | decide) | (norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; done) | norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE])

theorem adjugate_divergence_four
    (A : _root_.OAI.Yau.Jets.Coord → Fin 4 → Fin 4 → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hA : ∀ i j, DifferentiableAt ℝ (fun z ↦ A z i j) x)
    (hclosed : ∀ a i j, fderiv ℝ (fun z ↦ A z a j) x (Pi.single i 1) =
      fderiv ℝ (fun z ↦ A z a i) x (Pi.single j 1)) (a : Fin 4) :
    ∑ i : Fin 4, fderiv ℝ (fun z ↦ Matrix.adjugate (A z) i a) x (Pi.single i 1) = 0 := by
  simp_rw [adjugate_four_explicit]
  fin_cases a
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ (A z 1 1 * A z 2 2 * A z 3 3 - A z 1 1 * A z 2 3 * A z 3 2 - A z 1 2 * A z 2 1 * A z 3 3 + A z 1 2 * A z 2 3 * A z 3 1 + A z 1 3 * A z 2 1 * A z 3 2 - A z 1 3 * A z 2 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ -(A z 1 0 * A z 2 2 * A z 3 3 - A z 1 0 * A z 2 3 * A z 3 2 - A z 1 2 * A z 2 0 * A z 3 3 + A z 1 2 * A z 2 3 * A z 3 0 + A z 1 3 * A z 2 0 * A z 3 2 - A z 1 3 * A z 2 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ (A z 1 0 * A z 2 1 * A z 3 3 - A z 1 0 * A z 2 3 * A z 3 1 - A z 1 1 * A z 2 0 * A z 3 3 + A z 1 1 * A z 2 3 * A z 3 0 + A z 1 3 * A z 2 0 * A z 3 1 - A z 1 3 * A z 2 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ -(A z 1 0 * A z 2 1 * A z 3 2 - A z 1 0 * A z 2 2 * A z 3 1 - A z 1 1 * A z 2 0 * A z 3 2 + A z 1 1 * A z 2 2 * A z 3 0 + A z 1 2 * A z 2 0 * A z 3 1 - A z 1 2 * A z 2 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ -(A z 0 1 * A z 2 2 * A z 3 3 - A z 0 1 * A z 2 3 * A z 3 2 - A z 0 2 * A z 2 1 * A z 3 3 + A z 0 2 * A z 2 3 * A z 3 1 + A z 0 3 * A z 2 1 * A z 3 2 - A z 0 3 * A z 2 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 2 2 * A z 3 3 - A z 0 0 * A z 2 3 * A z 3 2 - A z 0 2 * A z 2 0 * A z 3 3 + A z 0 2 * A z 2 3 * A z 3 0 + A z 0 3 * A z 2 0 * A z 3 2 - A z 0 3 * A z 2 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 2 1 * A z 3 3 - A z 0 0 * A z 2 3 * A z 3 1 - A z 0 1 * A z 2 0 * A z 3 3 + A z 0 1 * A z 2 3 * A z 3 0 + A z 0 3 * A z 2 0 * A z 3 1 - A z 0 3 * A z 2 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 2 1 * A z 3 2 - A z 0 0 * A z 2 2 * A z 3 1 - A z 0 1 * A z 2 0 * A z 3 2 + A z 0 1 * A z 2 2 * A z 3 0 + A z 0 2 * A z 2 0 * A z 3 1 - A z 0 2 * A z 2 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ (A z 0 1 * A z 1 2 * A z 3 3 - A z 0 1 * A z 1 3 * A z 3 2 - A z 0 2 * A z 1 1 * A z 3 3 + A z 0 2 * A z 1 3 * A z 3 1 + A z 0 3 * A z 1 1 * A z 3 2 - A z 0 3 * A z 1 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 2 * A z 3 3 - A z 0 0 * A z 1 3 * A z 3 2 - A z 0 2 * A z 1 0 * A z 3 3 + A z 0 2 * A z 1 3 * A z 3 0 + A z 0 3 * A z 1 0 * A z 3 2 - A z 0 3 * A z 1 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 1 * A z 3 3 - A z 0 0 * A z 1 3 * A z 3 1 - A z 0 1 * A z 1 0 * A z 3 3 + A z 0 1 * A z 1 3 * A z 3 0 + A z 0 3 * A z 1 0 * A z 3 1 - A z 0 3 * A z 1 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 1 * A z 3 2 - A z 0 0 * A z 1 2 * A z 3 1 - A z 0 1 * A z 1 0 * A z 3 2 + A z 0 1 * A z 1 2 * A z 3 0 + A z 0 2 * A z 1 0 * A z 3 1 - A z 0 2 * A z 1 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ -(A z 0 1 * A z 1 2 * A z 2 3 - A z 0 1 * A z 1 3 * A z 2 2 - A z 0 2 * A z 1 1 * A z 2 3 + A z 0 2 * A z 1 3 * A z 2 1 + A z 0 3 * A z 1 1 * A z 2 2 - A z 0 3 * A z 1 2 * A z 2 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 2 * A z 2 3 - A z 0 0 * A z 1 3 * A z 2 2 - A z 0 2 * A z 1 0 * A z 2 3 + A z 0 2 * A z 1 3 * A z 2 0 + A z 0 3 * A z 1 0 * A z 2 2 - A z 0 3 * A z 1 2 * A z 2 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 1 * A z 2 3 - A z 0 0 * A z 1 3 * A z 2 1 - A z 0 1 * A z 1 0 * A z 2 3 + A z 0 1 * A z 1 3 * A z 2 0 + A z 0 3 * A z 1 0 * A z 2 1 - A z 0 3 * A z 1 1 * A z 2 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 1 * A z 2 2 - A z 0 0 * A z 1 2 * A z 2 1 - A z 0 1 * A z 1 0 * A z 2 2 + A z 0 1 * A z 1 2 * A z 2 0 + A z 0 2 * A z 1 0 * A z 2 1 - A z 0 2 * A z 1 1 * A z 2 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2]
    ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_JacobianCalculus
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

lemma jacobian_smooth (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ jacobian F x i j) :=
  (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

lemma jacobian_closed (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (x : _root_.OAI.Yau.Jets.Coord) (a i j : Fin 4) :
    fderiv ℝ (fun z ↦ jacobian F z a j) x (Pi.single i 1) =
      fderiv ℝ (fun z ↦ jacobian F z a i) x (Pi.single j 1) := by
  have hd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have he (k : Fin 4) : fderiv ℝ (fun z ↦ jacobian F z a k) x =
      (ContinuousLinearMap.proj a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).comp
        ((fderiv ℝ (fun z ↦ fderiv ℝ F z) x).flip (Pi.single k 1)) := by
    change fderiv ℝ ((ContinuousLinearMap.proj a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) ∘
      (fun z ↦ fderiv ℝ F z (Pi.single k 1))) x = _
    rw [fderiv_comp x (ContinuousLinearMap.proj a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).differentiableAt
      (hd.clm_apply (differentiableAt_const _)), ContinuousLinearMap.fderiv]
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he,he]
  exact congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v a)
    (hF.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Pi.single i 1) (Pi.single j 1))

lemma clm_coord_sum (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ) (v : _root_.OAI.Yau.Jets.Coord) :
    L v = ∑ j : Fin 4, (v j : ℂ) * L (Pi.single j 1) := by
  have hv : v = ∑ j : Fin 4, v j • Pi.single j (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, Complex.real_smul]

lemma coordPartial_comp (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hF : DifferentiableAt ℝ F x) (u : _root_.OAI.Yau.Jets.Coord → ℂ)
    (hu : DifferentiableAt ℝ u (F x)) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (u ∘ F) x =
      ∑ j : Fin 4, (jacobian F x j i : ℂ) * _root_.OAI.Yau.Jets.coordPartial j u (F x) := by
  unfold _root_.OAI.Yau.Jets.coordPartial
  rw [fderiv_comp x hu hF]
  exact clm_coord_sum (fderiv ℝ u (F x)) (fderiv ℝ F x (Pi.single i 1))

lemma coordPartial_sum_at (f : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ∑ j, f j z) x = ∑ j, _root_.OAI.Yau.Jets.coordPartial i (f j) x := by
  unfold _root_.OAI.Yau.Jets.coordPartial
  rw [fderiv_fun_sum (fun j _ ↦ hf j)]
  simp

lemma adjugate_entry_smooth (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun z ↦ (jacobian F z).adjugate i j) := by
  simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three,
    Matrix.submatrix_apply]
  have hJ := jacobian_smooth F hF
  fun_prop

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PiolaFlux
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

lemma adjugate_divergence_complex (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (x : _root_.OAI.Yau.Jets.Coord) (a : Fin 4) :
    ∑ i, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x = 0 := by
  simp_rw [coordPartial_ofReal_at _ x
    ((adjugate_entry_smooth F hF _ _).differentiable (by simp) x)]
  rw [← Complex.ofReal_sum, adjugate_divergence_four (jacobian F) x
    (fun i j ↦ (jacobian_smooth F hF i j).differentiable (by simp) x)
    (jacobian_closed F hF x)]
  rfl

lemma jacobian_mul_adjugate_complex (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) (a b : Fin 4) :
    ∑ i, ((jacobian F x).adjugate i a : ℂ) * (jacobian F x b i : ℂ) =
      if b=a then ((jacobian F x).det : ℂ) else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ ↦ M b a)
    (Matrix.mul_adjugate (jacobian F x))
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  have hh := congrArg Complex.ofReal h
  push_cast at hh
  split_ifs with hba <;> simp [hba,mul_comm] at hh ⊢ <;> exact hh

theorem signedPiola_divergence (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x)) :
    complexDivergence (signedPiola F V) x =
      ((jacobian F x).det : ℂ) * complexDivergence V (F x) := by
  have hFc (i a : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((adjugate_entry_smooth F hF i a).differentiable (by simp) x)
  have hVc (a : Fin 4) : DifferentiableAt ℝ (V a ∘ F) x :=
    (hV a).comp x (hF.differentiable (by simp) x)
  have hsum (i : Fin 4) : _root_.OAI.Yau.Jets.coordPartial i (signedPiola F V i) x =
      ∑ a, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ) * V a (F z)) x :=
    coordPartial_sum_at _ x (fun a ↦ (hFc i a).mul (hVc a)) i
  have hprod (i a : Fin 4) := coordPartial_mul_at
    (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) (fun z ↦ V a (F z)) x (hFc i a) (hVc a) i
  unfold complexDivergence
  simp_rw [hsum,hprod]
  simp only [Finset.sum_add_distrib]
  have hz : (∑ i, ∑ a, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x *
      V a (F x)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, adjugate_divergence_complex F hF x]
    simp
  rw [hz, zero_add]
  have hc (a i : Fin 4) := coordPartial_comp F x
    (hF.differentiable (by simp) x) (V a) (hV a) i
  simp only [Function.comp_def] at hc
  simp_rw [hc]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by rfl)
  calc
    _ = ∑ a, ∑ b, (∑ i, ((jacobian F x).adjugate i a : ℂ) *
        (jacobian F x b i : ℂ)) * _root_.OAI.Yau.Jets.coordPartial b (V a) (F x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by
      simp_rw [jacobian_mul_adjugate_complex]
      simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AbsolutePiola
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma local_absolute_ratio (d : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hd : ContinuousAt d x) (hn : d x ≠ 0) :
    ∃ s : ℝ, s * d x = |d x| ∧ ∀ᶠ z in 𝓝 x, |d z| / d z = s := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨-1, by simp [abs_of_neg hneg], ?_⟩
    filter_upwards [hd.eventually (gt_mem_nhds hneg)] with z hz
    simp [abs_of_neg hz, ne_of_lt hz]
  · refine ⟨1, by simp [abs_of_pos hpos], ?_⟩
    filter_upwards [hd.eventually (lt_mem_nhds hpos)] with z hz
    simp [abs_of_pos hz, ne_of_gt hz]

lemma signedPiola_differentiableAt (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x)) (i : Fin 4) :
    DifferentiableAt ℝ (signedPiola F V i) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  exact (Complex.ofRealCLM.differentiableAt.comp x
    ((adjugate_entry_smooth F hF i a).differentiable (by simp) x)).mul
      ((hV a).comp x (hF.differentiable (by simp) x))

theorem absolutePiola_divergence (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x))
    (hdet : (jacobian F x).det ≠ 0) :
    complexDivergence (absolutePiola F V) x =
      ((|(jacobian F x).det| : ℝ) : ℂ) * complexDivergence V (F x) := by
  have hd : ContinuousAt (fun z ↦ (jacobian F z).det) x :=
    (coordDet_smooth.continuous.comp (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous).continuousAt
  obtain ⟨s,hs,hr⟩ := local_absolute_ratio _ x hd hdet
  have he (i : Fin 4) : absolutePiola F V i =ᶠ[𝓝 x]
      fun z ↦ (s:ℂ) * signedPiola F V i z := by
    filter_upwards [hr] with z hz
    simp only [absolutePiola,hz]
  have hpartial (i : Fin 4) : _root_.OAI.Yau.Jets.coordPartial i (absolutePiola F V i) x =
      (s:ℂ) * _root_.OAI.Yau.Jets.coordPartial i (signedPiola F V i) x := by
    unfold _root_.OAI.Yau.Jets.coordPartial
    rw [(he i).fderiv_eq]
    rw [fderiv_const_mul (signedPiola_differentiableAt F hF V x hV i)]
    simp
  unfold complexDivergence
  simp_rw [hpartial]
  rw [← Finset.mul_sum]
  change (s:ℂ) * complexDivergence (signedPiola F V) x = _
  rw [signedPiola_divergence F hF V x hV, ← mul_assoc, ← Complex.ofReal_mul, hs]
  rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma sphereRoundChartMatrix_posDef (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) : (sphereRoundChartMatrix p y).PosDef := by
  simpa [sphereRoundChartMatrix,conjTranspose_eq_transpose_of_trivial] using
    (PosDef.one : (1 : Matrix (Fin 5) (Fin 5) ℝ).PosDef).conjTranspose_mul_mul_same
      (sphereChartFrame_injective p hy)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalMatrixSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype n] [DecidableEq n] in
lemma matrix_gram_smooth_at (J : E → Matrix m n ℝ) {x : E}
    (hJ : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ J z i j) x) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ ((J z).transpose * J z) i j) x := by
  simp only [mul_apply,transpose_apply]
  exact ContDiffAt.sum (fun k _ ↦ (hJ k i).mul (hJ k j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_BaseChartFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma roundChartDensity_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (roundChartDensity p) z := by
  exact (matrix_det_smooth_at _ (matrix_gram_smooth_at _ (sphereChartFrame_smooth_at p hz))).sqrt
    (sphereRoundChartMatrix_posDef p hz).det_pos.ne'

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSmoothExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem compact_smooth_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  have hsupp : tsupport G ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [G,hz])
  refine ⟨G,hG,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_⟩
  intro x hx
  filter_upwards [hb1 x hx] with z hz
  simp [G,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalPiolaDivergence
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

lemma local_absolutePiola_divergence (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) {U : Set _root_.OAI.Yau.Jets.Coord}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ U) (hV : ∀ a, DifferentiableAt ℝ (V a) (F x))
    (hdet : (jacobian F x).det ≠ 0) :
    complexDivergence (absolutePiola F V) x =
      ((|(jacobian F x).det| : ℝ) : ℂ) * complexDivergence V (F x) := by
  obtain ⟨G,hG,_,_,hge⟩ := compact_smooth_extension isCompact_singleton hU
    (singleton_subset_iff.mpr hx) F hF
  have he := hge x (mem_singleton x)
  have hj : jacobian G =ᶠ[𝓝 x] jacobian F := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    unfold jacobian
    rw [hy]
  have hp (i : Fin 4) : absolutePiola G V i =ᶠ[𝓝 x] absolutePiola F V i := by
    filter_upwards [he,hj] with y hy hjy
    simp only [absolutePiola,signedPiola,hy,hjy]
  have hdiv : complexDivergence (absolutePiola G V) x =
      complexDivergence (absolutePiola F V) x := by
    unfold complexDivergence _root_.OAI.Yau.Jets.coordPartial
    apply Finset.sum_congr rfl
    intro i _
    rw [(hp i).fderiv_eq]
  have h := absolutePiola_divergence G hG V x (by simpa only [he.eq_of_nhds] using hV)
    (by simpa only [hj.eq_of_nhds] using hdet)
  simpa only [hdiv,hj.eq_of_nhds,he.eq_of_nhds] using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedChartOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma seedCoordPartial_pullback (f : BaseModel → ℝ) (hf : Differentiable ℝ f)
    (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ (f (seedCoordEquiv z):ℂ)) x =
      (fderiv ℝ f (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i):ℂ) := by
  have hh : DifferentiableAt ℝ (fun z ↦ f (seedCoordEquiv z)) x :=
    (hf _).comp x seedCoordEquiv.differentiableAt
  rw [coordPartial_ofReal_at (fun z ↦ f (seedCoordEquiv z)) x hh]
  change (fderiv ℝ (f ∘ seedCoordEquiv) x (Pi.single i 1):ℂ) = _
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma intrinsicRoundFlux_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (intrinsicRoundFlux A f p i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hz : z ∈ (extChartAt (𝓡 4) p).target := by rw [centeredSphereChart_target]; trivial
  apply (roundChartDensity_smooth_at p hz).mul
  apply ContDiffAt.sum
  intro j _
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p hz i j).mul
    ((smooth_inverse_chart_derivative f hf p hz).clm_apply contDiffAt_const)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTransition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphereChartTransition_derivative_inverse (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    (fderiv ℝ (sphereChartTransition q p) (sphereChartTransition p q x)).comp
      (fderiv ℝ (sphereChartTransition p q) x) = ContinuousLinearMap.id ℝ Yau.Jets.Coord := by
  have hp := (sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)
  have hq := (sphereChartTransition_smoothOn q p).contDiffAt
    ((sphereChartTransitionDomain_open q p).mem_nhds (sphereChartTransition_mem p q hx))
  have he : (sphereChartTransition q p) ∘ (sphereChartTransition p q) =ᶠ[𝓝 x] id := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    exact sphereChartTransition_inverse p q hy
  rw [← fderiv_comp x (hq.differentiableAt (by simp)) (hp.differentiableAt (by simp)),
    he.fderiv_eq,fderiv_id]

lemma sphereChartTransition_jacobian_ne_zero (p q : Base) {x : Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) : (jacobian (sphereChartTransition p q) x).det ≠ 0 := by
  have hleft := sphereChartTransition_derivative_inverse p q hx
  have hright := sphereChartTransition_derivative_inverse q p (sphereChartTransition_mem p q hx)
  rw [sphereChartTransition_inverse p q hx] at hright
  have hi : (fderiv ℝ (sphereChartTransition p q) x).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hright hleft
  obtain ⟨e,he⟩ := hi
  change coordDet (fderiv ℝ (sphereChartTransition p q) x) ≠ 0
  rw [← he]
  exact coordDet_equiv_ne_zero e

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereTransitionScalar
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphereScalarPullback_smooth (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ (f (sphereChartCoordMap p x) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hf.comp (sphereChartCoordMap_smooth p)).contDiff

lemma sphereScalarPartial_eq (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) :
    (sphereScalarPartial f p i x : ℂ) =
      _root_.OAI.Yau.Jets.coordPartial i (fun y ↦ (f (sphereChartCoordMap p y) : ℂ)) x := by
  symm
  exact seedCoordPartial_pullback _ (fun z ↦
    (smooth_inverse_chart_comp f hf p (by rw [centeredSphereChart_target]; trivial)).differentiableAt
      (by simp)) i x

lemma sphereChartTransition_scalar (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) (i : Fin 4) :
    sphereScalarPartial f p i x = ∑ j,
      jacobian (sphereChartTransition p q) x j i *
        sphereScalarPartial f q j (sphereChartTransition p q x) := by
  have he : (fun y ↦ (f (sphereChartCoordMap p y) : ℂ)) =ᶠ[𝓝 x]
      (fun y ↦ (f (sphereChartCoordMap q y) : ℂ)) ∘ sphereChartTransition p q := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    simp only [Function.comp_apply,sphereChartTransition_point p q hy]
  have hF := (sphereChartTransition_smoothOn p q).contDiffAt
    ((sphereChartTransitionDomain_open p q).mem_nhds hx)
  have hd : _root_.OAI.Yau.Jets.coordPartial i (fun y ↦ (f (sphereChartCoordMap p y) : ℂ)) x =
      ∑ j, (jacobian (sphereChartTransition p q) x j i : ℂ) *
        _root_.OAI.Yau.Jets.coordPartial j (fun y ↦ (f (sphereChartCoordMap q y) : ℂ)) (sphereChartTransition p q x) := by
    unfold _root_.OAI.Yau.Jets.coordPartial
    rw [he.fderiv_eq]
    exact coordPartial_comp _ x (hF.differentiableAt (by simp)) _
      ((sphereScalarPullback_smooth f hf q).differentiable (by simp) _) i
  simp only [← sphereScalarPartial_eq f hf] at hd
  exact_mod_cast hd

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereTransitionTensor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry
open Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

lemma frameLeftInverse_transition (F : Matrix m n ℝ) (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    frameLeftInverse (F*J) = J⁻¹*frameLeftInverse F := by
  have hg : (F*J).transpose*(F*J) = J.transpose*(F.transpose*F)*J := by simp [Matrix.mul_assoc]
  have ht : IsUnit J.transpose.det := by simpa using (isUnit_iff_ne_zero.mpr hJ)
  rw [frameLeftInverse,hg,Matrix.mul_inv_rev,Matrix.mul_inv_rev,transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc J.transpose⁻¹ J.transpose F.transpose,Matrix.nonsing_inv_mul _ ht,Matrix.one_mul]
  rfl

lemma frameContravariant_transition (A : Matrix m m ℝ) (F : Matrix m n ℝ)
    (J : Matrix n n ℝ) (hJ : J.det ≠ 0) :
    frameContravariant A (F*J) = J⁻¹*frameContravariant A F*J⁻¹.transpose := by
  simp only [frameContravariant_pullback,frameLeftInverse_transition F J hJ,
    transpose_mul,Matrix.mul_assoc]

end Yau.Geometry
namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix

lemma sphereChartTransition_tensor (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (p q : Base) {x : Yau.Jets.Coord} (hx : x ∈ sphereChartTransitionDomain p q) :
    sphereChartTensor A p (seedCoordEquiv x) =
      (jacobian (sphereChartTransition p q) x)⁻¹ *
        sphereChartTensor A q (seedCoordEquiv (sphereChartTransition p q x)) *
          ((jacobian (sphereChartTransition p q) x)⁻¹).transpose := by
  change frameContravariant (A (sphereChartCoordMap p x)) (sphereChartFrame p (seedCoordEquiv x)) =
    _*frameContravariant (A (sphereChartCoordMap q (sphereChartTransition p q x))) _*_
  rw [sphereChartTransition_point p q hx,sphereChartTransition_frame p q hx,
    frameContravariant_transition _ _ _ (sphereChartTransition_jacobian_ne_zero p q hx)]

lemma sphereChartTransition_intrinsic_tensor (A : IntrinsicTensor)
    (p q : Base) {x : Yau.Jets.Coord} (hx : x ∈ sphereChartTransitionDomain p q) :
    intrinsicSphereChartTensor A p (seedCoordEquiv x) =
      (jacobian (sphereChartTransition p q) x)⁻¹ *
        intrinsicSphereChartTensor A q (seedCoordEquiv (sphereChartTransition p q x)) *
          ((jacobian (sphereChartTransition p q) x)⁻¹).transpose := by
  simp only [intrinsicSphereChartTensor_eq]
  exact sphereChartTransition_tensor _ p q hx

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereTransitionFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry
open Matrix

lemma inverse_contravariant_gradient (J B : Matrix (Fin 4) (Fin 4) ℝ)
    (hJ : J.det ≠ 0) (v : Fin 4 → ℝ) :
    (J⁻¹ * B * J⁻¹.transpose).mulVec (J.transpose.mulVec v) =
      J⁻¹.mulVec (B.mulVec v) := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,Matrix.transpose_nonsing_inv,
    Matrix.nonsing_inv_mul _ (by simpa using (isUnit_iff_ne_zero.mpr hJ)),Matrix.mul_one,
    ← Matrix.mulVec_mulVec]

lemma absolute_inverse_flux (J : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    |J.det| * (J⁻¹.mulVec v) i = |J.det| / J.det * ∑ j, J.adjugate i j * v j := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.mulVec,Matrix.smul_apply,
    smul_eq_mul,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Yau.Geometry
namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Matrix
open scoped ContDiff

lemma sphereChartTransition_flux (A : IntrinsicTensor) (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) (i : Fin 4) :
    sphereCoordFlux A f p i x =
      absolutePiola (sphereChartTransition p q) (sphereCoordFlux A f q) i x := by
  let J := jacobian (sphereChartTransition p q) x
  let B := intrinsicSphereChartTensor A q (seedCoordEquiv (sphereChartTransition p q x))
  let v := fun j ↦ sphereScalarPartial f q j (sphereChartTransition p q x)
  have hg : (fun j ↦ sphereScalarPartial f p j x) = J.transpose.mulVec v := by
    funext j
    exact sphereChartTransition_scalar f hf p q hx j
  have ht := inverse_contravariant_gradient J B (sphereChartTransition_jacobian_ne_zero p q hx) v
  have hreal : intrinsicRoundFlux A f p i (seedCoordEquiv x) =
      |J.det| / J.det * ∑ j, J.adjugate i j *
        intrinsicRoundFlux A f q j (seedCoordEquiv (sphereChartTransition p q x)) := by
    change roundChartDensity p (seedCoordEquiv x) *
      ((intrinsicSphereChartTensor A p (seedCoordEquiv x)).mulVec
        (fun j ↦ sphereScalarPartial f p j x)) i = _
    rw [sphereChartTransition_round_density p q hx,sphereChartTransition_intrinsic_tensor A p q hx,hg]
    change (|J.det| * _) * ((J⁻¹*B*J⁻¹.transpose).mulVec (J.transpose.mulVec v)) i = _
    rw [ht]
    calc
      _ = roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)) *
          (|J.det| * (J⁻¹.mulVec (B.mulVec v)) i) := by ring
      _ = _ := by
        rw [absolute_inverse_flux]
        change _ = |J.det| / J.det * ∑ j, J.adjugate i j *
          (roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)) * (B.mulVec v) j)
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  unfold sphereCoordFlux absolutePiola signedPiola
  dsimp only
  dsimp only [J] at hreal
  exact_mod_cast hreal

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereOperatorInvariance
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)

include hA hs hp hf

lemma sphereCoordFlux_smooth (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (sphereCoordFlux A f p i) :=
  Complex.ofRealCLM.contDiff.comp
    ((intrinsicRoundFlux_smooth A hA hs hp f hf p i).comp seedCoordEquiv.contDiff)

lemma sphereChartTransition_divergence_oai (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    complexDivergence (sphereCoordFlux A f p) x =
      (|(jacobian (sphereChartTransition p q) x).det| : ℝ) *
        complexDivergence (sphereCoordFlux A f q) (sphereChartTransition p q x) := by
  have he (i : Fin 4) : sphereCoordFlux A f p i =ᶠ[𝓝 x]
      absolutePiola (sphereChartTransition p q) (sphereCoordFlux A f q) i := by
    filter_upwards [(sphereChartTransitionDomain_open p q).mem_nhds hx] with y hy
    exact sphereChartTransition_flux A f hf p q hy i
  have hd : complexDivergence (sphereCoordFlux A f p) x =
      complexDivergence (absolutePiola (sphereChartTransition p q) (sphereCoordFlux A f q)) x := by
    unfold complexDivergence _root_.OAI.Yau.Jets.coordPartial
    apply Finset.sum_congr rfl
    intro i _
    rw [(he i).fderiv_eq]
  rw [hd]
  exact local_absolutePiola_divergence _ (sphereChartTransitionDomain_open p q)
    (sphereChartTransition_smoothOn p q) _ x hx
    (fun i ↦ (sphereCoordFlux_smooth A hA hs hp f hf q i).differentiable (by simp) _)
    (sphereChartTransition_jacobian_ne_zero p q hx)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphereChartTransition_divergence_oai := @OAI.Yau.Target.sphereChartTransition_divergence_oai
