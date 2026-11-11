-- Prove2me | solution 1 for OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:34.822354+00:00
-- url     : https://prove2.me/submissions/6d050719-3185-4777-a6ac-6cd607e67d34

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_exists_sphere_simplicity_kernel_form
import Theorems.Thm_OAI_Yau_Target_sphere_affine_kernel_implies_simplicity

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FiniteChartDerivativeSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finiteChartDerivativeValues_nonempty (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) :
    (finiteChartDerivativeValues P Q J f).Nonempty := ⟨0,Or.inl rfl⟩

lemma finiteChartDerivativeValues_bddAbove (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    BddAbove (finiteChartDerivativeValues P Q J f) := by
  classical
  have hb (p : P) (i : Fin (J+1)) : ∃ C : ℝ, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val (f p) x‖ ≤ C :=
    hQ.exists_bound_of_continuousOn ((hf p p.property).continuous_iteratedFDeriv
      (by exact_mod_cast (show (i.val:ℕ∞) ≤ ⊤ from le_top))).continuousOn
  choose C hC using hb
  let B : ℝ := 1+∑ p : P, ∑ i, |C p i|
  have hsum : 0 ≤ ∑ p : P, ∑ i, |C p i| :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
  refine ⟨B,?_⟩
  rintro t (ht | ⟨p,hp,i,hi,x,hx,rfl⟩)
  · have ht0 : t=0 := ht
    rw [ht0]
    change 0 ≤ 1+∑ p : P, ∑ i, |C p i|
    linarith
  · let pi : P := ⟨p,hp⟩
    let ii : Fin (J+1) := ⟨i,by omega⟩
    have hci : C pi ii ≤ ∑ p : P, ∑ j, |C p j| :=
      (le_abs_self _).trans ((Finset.single_le_sum (fun j _ ↦ abs_nonneg (C pi j)) (Finset.mem_univ ii)).trans
        (Finset.single_le_sum (fun p _ ↦ Finset.sum_nonneg (fun j _ ↦ abs_nonneg (C p j))) (Finset.mem_univ pi)))
    exact (hC pi ii x hx).trans (by change C pi ii ≤ 1+∑ p : P, ∑ j, |C p j|; linarith)

lemma finiteChartDerivativeSize_le (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p ∈ P, ∀ i, i ≤ J → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ i (f p) x‖ ≤ C) : finiteChartDerivativeSize P Q J f ≤ C := by
  apply csSup_le (finiteChartDerivativeValues_nonempty P Q J f)
  rintro t (ht | ⟨p,hp,i,hi,x,hx,rfl⟩)
  · have ht0 : t=0 := ht
    simpa only [ht0] using hC
  · exact hb p hp i hi x hx

lemma finiteChartDerivativeSize_nonneg (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    0 ≤ finiteChartDerivativeSize P Q J f :=
  le_csSup (finiteChartDerivativeValues_bddAbove P hQ J f hf) (Or.inl rfl)

lemma norm_le_finiteChartDerivativeSize (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p))
    (p : I) (hp : p ∈ P) (i : ℕ) (hi : i ≤ J) (x : E) (hx : x ∈ Q) :
    ‖iteratedFDeriv ℝ i (f p) x‖ ≤ finiteChartDerivativeSize P Q J f :=
  le_csSup (finiteChartDerivativeValues_bddAbove P hQ J f hf) (Or.inr ⟨p,hp,i,hi,x,hx,rfl⟩)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FiniteChartDerivativeSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finiteChartDerivativeSize_zero (P : Finset I) {Q : Set E} (hQ : IsCompact Q) (J : ℕ) :
    finiteChartDerivativeSize P Q J (fun _ _ ↦ (0:F)) = 0 := by
  apply le_antisymm
  · exact finiteChartDerivativeSize_le P Q J _ le_rfl (by intros; simp)
  · exact finiteChartDerivativeSize_nonneg P hQ J _ (fun _ _ ↦ contDiff_const)

lemma finiteChartDerivativeSize_smul_le (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (r : ℝ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ r • f p x) ≤ ‖r‖*finiteChartDerivativeSize P Q J f := by
  apply finiteChartDerivativeSize_le _ _ _ _
    (mul_nonneg (norm_nonneg r) (finiteChartDerivativeSize_nonneg P hQ J f hf))
  intro p hp i hi x hx
  rw [iteratedFDeriv_const_smul_apply'
    ((hf p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_le_finiteChartDerivativeSize P hQ J f hf p hp i hi x hx) (norm_nonneg r)

lemma finiteChartDerivativeSize_smul (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (r : ℝ) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ r • f p x) = ‖r‖*finiteChartDerivativeSize P Q J f := by
  by_cases hr : r=0
  · subst r
    simpa using finiteChartDerivativeSize_zero (F := F) P hQ J
  · apply le_antisymm (finiteChartDerivativeSize_smul_le P hQ J r f hf)
    have h := finiteChartDerivativeSize_smul_le P hQ J r⁻¹ (fun p x ↦ r • f p x)
      (fun p hp ↦ (hf p hp).const_smul r)
    simp only [smul_smul,inv_mul_cancel₀ hr,one_smul] at h
    have hh := mul_le_mul_of_nonneg_left h (norm_nonneg r)
    simpa only [norm_inv,← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr),one_mul] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereRadialProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped RealInnerProductSpace
noncomputable section

lemma sphere_radial_norm (x : Base) : ‖(x : AmbientBase)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using x.property

lemma sphereTangentProjection_orthogonal (x : Base) (v : AmbientBase) :
    ⟪(x : AmbientBase),sphereTangentProjection x v⟫ = 0 := by
  simp [sphereTangentProjection, inner_sub_right, real_inner_smul_right]

lemma sphereTangentProjection_restriction (x : Base) (v : AmbientBase) :
    sphereCovectorRestriction x (sphereTangentProjection x v) = sphereCovectorRestriction x v := by
  simp only [sphereTangentProjection,map_sub,map_smul,sphereCovectorRestriction_radial,
    smul_zero,sub_zero]

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJetContinuityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma linearCovectorPull_apply (e : F ≃L[ℝ] E) (α : E →L[ℝ] ℝ) (u : F) :
    linearCovectorPull e α u = α (e u) := rfl

lemma linearMetricField_positive (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) :
    ∀ v, v ≠ 0 → 0 < linearMetricField e g x v v := by
  intro v hv
  exact hp (e v) (by intro h; exact hv (e.injective (h.trans e.map_zero.symm)))

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveContravariant
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coefficientMetric_positive (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α)) (hρ : 0 < c.2) (v : E) (hv : v ≠ 0) :
    0 < coefficientMetricValue c v v := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have he : e.symm v ≠ 0 := by
    intro hz
    have h := congrArg e hz
    exact hv (by simpa using h)
  have hh := hp (e.symm v) he
  change 0 < e.symm v (e (e.symm v)) at hh
  rw [e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using mul_pos hρ hh

lemma coefficientMetric_inverse (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α)) (hρ : 0 < c.2) :
    ContinuousLinearMap.inverse (coefficientMetricValue c) = c.2⁻¹ • c.1 := by
  let e := positiveContravariantEquiv c.1 hp
  let m := positiveMetricEquiv (coefficientMetricValue c) (coefficientMetric_positive c hp hρ)
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have hm : ContinuousLinearMap.inverse (coefficientMetricValue c) = m.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv m
  rw [hm]
  ext α
  apply m.injective
  change m (m.symm α) = coefficientMetricValue c (c.2⁻¹ • c.1 α)
  rw [m.apply_symm_apply]
  change α = c.2 • (ContinuousLinearMap.inverse c.1) (c.2⁻¹ • e α)
  rw [hi,map_smul]
  change α = c.2 • (c.2⁻¹ • e.symm (e α))
  simp [smul_smul,hρ.ne']

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

lemma baseCovectorCoordinates_apply (α : BaseModel →L[ℝ] ℝ) (v : BaseModel) :
    α v = baseCovectorCoordinates α ⬝ᵥ WithLp.ofLp v := by
  have hv := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp [baseCovectorCoordinates,map_sum,map_smul,dotProduct,mul_comm]

lemma baseCovectorCoordinates_injective : Function.Injective baseCovectorCoordinates := by
  intro α β h
  ext v
  rw [baseCovectorCoordinates_apply,baseCovectorCoordinates_apply,h]

lemma baseCovectorCoordinates_ne_zero {α : BaseModel →L[ℝ] ℝ} (hα : α ≠ 0) :
    baseCovectorCoordinates α ≠ 0 := by
  intro h
  exact hα (baseCovectorCoordinates_injective (h.trans (by ext i; rfl)))

lemma matrixContravariant_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ)
    (α : BaseModel →L[ℝ] ℝ) :
    WithLp.ofLp (matrixContravariant A α) = A *ᵥ baseCovectorCoordinates α := by
  ext k
  simp [matrixContravariant,baseCovectorCoordinates,mulVec,dotProduct,
    EuclideanSpace.basisFun_apply,Pi.single_apply,ite_mul,mul_ite,mul_comm]

lemma matrixContravariant_pair (A : Matrix (Fin 4) (Fin 4) ℝ) (α β : BaseModel →L[ℝ] ℝ) :
    α (matrixContravariant A β) = baseCovectorCoordinates α ⬝ᵥ (A *ᵥ baseCovectorCoordinates β) := by
  rw [baseCovectorCoordinates_apply,matrixContravariant_coordinates]

lemma matrixContravariant_positive (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) : 0 < α (matrixContravariant A α) := by
  rw [matrixContravariant_pair]
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos (baseCovectorCoordinates_ne_zero hα)

lemma matrixCovariant_coordinates (B : Matrix (Fin 4) (Fin 4) ℝ) (v : BaseModel) :
    baseCovectorCoordinates (matrixCovariant B v) = B *ᵥ WithLp.ofLp v := by
  ext k
  simp [baseCovectorCoordinates,matrixCovariant,
    EuclideanSpace.inner_single_left,mulVec,dotProduct,mul_comm]

lemma matrixCovariant_apply (B : Matrix (Fin 4) (Fin 4) ℝ) (v w : BaseModel) :
    matrixCovariant B v w = (B *ᵥ WithLp.ofLp v) ⬝ᵥ WithLp.ofLp w := by
  rw [baseCovectorCoordinates_apply,matrixCovariant_coordinates]

lemma matrixContravariant_inverse (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsUnit A.det) :
    ContinuousLinearMap.inverse (matrixContravariant A) = matrixCovariant A⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  · ext v i
    change (matrixContravariant A (matrixCovariant A⁻¹ v)) i = v i
    have h := matrixContravariant_coordinates A (matrixCovariant A⁻¹ v)
    rw [matrixCovariant_coordinates,mulVec_mulVec,mul_nonsing_inv A hA,one_mulVec] at h
    exact congrFun h i
  · ext α v
    have h : baseCovectorCoordinates (matrixCovariant A⁻¹ (matrixContravariant A α)) =
        baseCovectorCoordinates α := by
      rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
        nonsing_inv_mul A hA,one_mulVec]
    exact congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β v) (baseCovectorCoordinates_injective h)

lemma matrixCovariant_smul (r : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixCovariant (r • B) = r • matrixCovariant B := by
  ext v w
  simp [matrixCovariant_apply,smul_mulVec,smul_dotProduct]

lemma coefficientMetric_matrix (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef) (ρ : ℝ) :
    coefficientMetricValue (matrixContravariant A,ρ) = matrixCovariant (ρ • A⁻¹) := by
  rw [coefficientMetricValue,matrixContravariant_inverse A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    matrixCovariant_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hs hp in
lemma intrinsicSphereChartTensor_posDef (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) : (intrinsicSphereChartTensor A p z).PosDef := by
  rw [intrinsicSphereChartTensor_eq]
  change (frameContravariant _ _).PosDef
  rw [sphereChart_contravariant _ (intrinsicAmbientMatrix_posDef A hs hp _) zero_lt_one p hz
    (intrinsicAmbientMatrix_radial A _),one_smul]
  exact (sphereWeightedChartMatrix_posDef _ (intrinsicAmbientMatrix_posDef A hs hp _)
    zero_lt_one p hz).inv

include hs hp in
lemma intrinsicChartCoefficient_positive (ρ : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) :
    0 < α ((intrinsicChartCoefficient A ρ p z).1 α) :=
  matrixContravariant_positive _ (intrinsicSphereChartTensor_posDef A hs hp p hz) α hα

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMetric
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x)

include hs hp hρ in
lemma intrinsicChartCoefficient_metric (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    coefficientMetricValue (intrinsicChartCoefficient A ρ p z) =
      matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p z) := by
  let B := intrinsicSphereChartTensor A p z
  let G := baseChartMetric (intrinsicAmbientMatrix A) ρ p z
  let r := ρ ((extChartAt (𝓡 4) p).symm z)
  have hr : 0 < r := hρ _
  have hB : B.PosDef := intrinsicSphereChartTensor_posDef A hs hp p hz
  have hG : G.PosDef := sphereWeightedChartMatrix_posDef _
    (intrinsicAmbientMatrix_posDef A hs hp _) hr p hz
  have hi : G⁻¹ = r⁻¹ • B := intrinsic_horizontal_inverse A hs hp ρ hρ p hz
  have hb : B = r • G⁻¹ := by rw [hi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hbi : B⁻¹ = r⁻¹ • G := by
    apply Matrix.inv_eq_left_inv
    rw [hb,smul_mul_assoc,mul_smul_comm,smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
      mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
  change coefficientMetricValue (matrixContravariant B,r) = matrixCovariant G
  rw [coefficientMetric_matrix B hB r,hbi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientSmooth
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hA hs hp in
lemma intrinsicChartCoefficient_smoothAt (ρ : Base → ℝ)
    (hρ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (intrinsicChartCoefficient A ρ p) z := by
  apply ContDiffAt.prodMk _ (smooth_inverse_chart_comp ρ hρ p hz)
  change ContDiffAt ℝ ∞ (fun w ↦ matrixContravariant (intrinsicSphereChartTensor A p w)) z
  unfold matrixContravariant
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p hz i j).smul contDiffAt_const

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundChartConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_5_rf4e1ae_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
lemma roundChartMetric_smooth (p : Base) : ContDiff ℝ ∞ (roundChartMetric p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have h := sphereChartDerivative_smooth_at p (y := y) (by rw [centeredSphereChart_target]; trivial)
  have hpre : ContMDiffAt 𝓘(ℝ,BaseModel)
      𝓘(ℝ,(AmbientBase →L[ℝ] ℝ) →L[ℝ] (BaseModel →L[ℝ] ℝ)) ∞
      (fun z ↦ (sphereChartDerivative p z).precomp ℝ) y := h.contMDiffAt.clm_precomp
  have hpost : ContMDiffAt 𝓘(ℝ,BaseModel) 𝓘(ℝ,BaseModel →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun z ↦ ambientRoundBilinear.comp (sphereChartDerivative p z)) y :=
    contMDiffAt_const.clm_comp h.contMDiffAt
  exact contMDiffAt_iff_contDiffAt.mp (hpre.clm_comp hpost)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCoefficientJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundCoefficients_smooth : ContDiff ℝ ∞ roundCoefficients := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (roundChartMetric seedPoint y) := by
    exact contDiffAt_map_inverse (positiveMetricEquiv _ (roundChartMetric_positive y))
  exact (hi.comp y (roundChartMetric_smooth seedPoint).contDiffAt).prodMk contDiffAt_const

lemma roundCoefficientJet_continuous : Continuous roundCoefficientJet :=
  roundCoefficients_smooth.continuous.prodMk (roundCoefficients_smooth.continuous_fderiv (by simp))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicSeedPatch
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma intrinsicSeedCoordMetric_eq (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x) :
    seedCoordMetric (intrinsicChartCoefficient A ρ seedPoint) = intrinsicSeedCoordMetric A ρ := by
  funext x
  change linearMetricPull seedCoordEquiv _ = linearMetricPull seedCoordEquiv _
  rw [Function.comp_apply,intrinsicChartCoefficient_metric A hs hp ρ hρ seedPoint
    (by rw [centeredSphereChart_target]; trivial)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedChartPrincipal
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

lemma linearMetricPull_inverse_covector
    (g : BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (α : BaseModel →L[ℝ] ℝ) :
    ContinuousLinearMap.inverse (linearMetricPull seedCoordEquiv g)
      (linearCovectorPull seedCoordEquiv α) =
      seedCoordEquiv.symm (ContinuousLinearMap.inverse g α) := by
  let e := positiveMetricEquiv g hp
  have hpp : ∀ v : _root_.OAI.Yau.Jets.Coord, v ≠ 0 → 0 < linearMetricPull seedCoordEquiv g v v :=
    linearMetricField_positive seedCoordEquiv (fun _ ↦ g) 0 hp
  let E := positiveMetricEquiv (linearMetricPull seedCoordEquiv g) hpp
  rw [show ContinuousLinearMap.inverse (linearMetricPull seedCoordEquiv g) =
    E.symm.toContinuousLinearMap from ContinuousLinearMap.inverse_equiv E,
    show ContinuousLinearMap.inverse g = e.symm.toContinuousLinearMap from
      ContinuousLinearMap.inverse_equiv e]
  apply E.injective
  change E (E.symm (linearCovectorPull seedCoordEquiv α)) = E (seedCoordEquiv.symm (e.symm α))
  rw [E.apply_symm_apply]
  ext v
  change α (seedCoordEquiv v) = g (seedCoordEquiv (seedCoordEquiv.symm (e.symm α)))
    (seedCoordEquiv v)
  rw [seedCoordEquiv.apply_symm_apply]
  exact (congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β (seedCoordEquiv v)) (e.apply_symm_apply α)).symm

lemma intrinsicSeedCoordMetric_principal (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ∀ x, 0 < rho x) (i j : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) :
    sourcePrincipal (intrinsicSeedCoordMetric A rho) i j x =
      (rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)))⁻¹ *
        intrinsicSphereChartTensor A seedPoint (seedCoordEquiv x) i j := by
  rw [← intrinsicSeedCoordMetric_eq A hs hp rho hr]
  let c := intrinsicChartCoefficient A rho seedPoint (seedCoordEquiv x)
  have hc : ∀ α : BaseModel →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α) :=
    intrinsicChartCoefficient_positive A hs hp rho seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  let α : BaseModel →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp seedCoordEquiv.symm.toContinuousLinearMap
  have he : linearCovectorPull seedCoordEquiv α = (ContinuousLinearMap.proj j : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) := by
    ext v
    simp [linearCovectorPull_apply,α]
  unfold sourcePrincipal seedCoordMetric linearMetricField
  change (ContinuousLinearMap.inverse (linearMetricPull seedCoordEquiv (coefficientMetricValue c))
    (ContinuousLinearMap.proj j)) i = _
  rw [← he,linearMetricPull_inverse_covector _ (coefficientMetric_positive c hc (hr _)),
    coefficientMetric_inverse c hc (hr _)]
  have hα : baseCovectorCoordinates α = Pi.single j 1 := by
    ext k
    change (seedCoordEquiv.symm (EuclideanSpace.basisFun (Fin 4) ℝ k)) j = _
    rw [← seedCoordEquiv_basis,seedCoordEquiv.symm_apply_apply]
    simp [Pi.single_apply,eq_comm]
  change (seedCoordEquiv.symm (c.2⁻¹ • matrixContravariant
    (intrinsicSphereChartTensor A seedPoint (seedCoordEquiv x)) α)) i = _
  change (WithLp.ofLp (c.2⁻¹ • matrixContravariant
    (intrinsicSphereChartTensor A seedPoint (seedCoordEquiv x)) α)) i = _
  simp [matrixContravariant_coordinates,hα,c,intrinsicChartCoefficient]

end
end Yau.Target

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

lemma intrinsicSeedCoordFlux (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (i : Fin 4) :
    sourceFlux (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (fun x ↦ (f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ)) i =
      fun x ↦ (intrinsicRoundFlux A f seedPoint i (seedCoordEquiv x):ℂ) := by
  have hf' : Differentiable ℝ (f ∘ (extChartAt (𝓡 4) seedPoint).symm) := fun z ↦
    (smooth_inverse_chart_comp f hf seedPoint
      (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)
  have hd (j : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) :
      _root_.OAI.Yau.Jets.coordPartial j (fun z ↦ (f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z)):ℂ)) x =
      (fderiv ℝ (f ∘ (extChartAt (𝓡 4) seedPoint).symm) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ j):ℂ) :=
    seedCoordPartial_pullback (f ∘ (extChartAt (𝓡 4) seedPoint).symm) hf' j x
  funext x
  simp only [sourceFlux,intrinsicSeedCoordMetric_principal A hs hp rho hr,
    hd,intrinsicRoundFlux,seedCoordWeight,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hne : (rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ) ≠ 0 := by
    exact_mod_cast (hr ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x))).ne'
  field_simp

theorem intrinsicSeedCoordOperator (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (x : _root_.OAI.Yau.Jets.Coord) :
    sourceWeightedOperator (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (fun z ↦ (f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z)):ℂ)) x =
      (intrinsicWeightedChartOperator A rho f seedPoint (seedCoordEquiv x):ℂ) := by
  simp only [sourceWeightedOperator,complexDivergence,
    intrinsicSeedCoordFlux A hs hp rho hr f hf,
    seedCoordPartial_pullback _ ((intrinsicRoundFlux_smooth A hA hs hp f hf _ _).differentiable (by simp)),
    intrinsicWeightedChartOperator,seedCoordWeight,Complex.ofReal_mul,
    Complex.ofReal_inv,Complex.ofReal_sum,_root_.mul_inv_rev]
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedChartScalarExtension
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

lemma seedSphereFromCoord_source (x : Yau.Jets.Coord) :
    seedSphereFromCoord x ∈ (extChartAt (𝓡 4) seedPoint).source :=
  (extChartAt (𝓡 4) seedPoint).map_target (by rw [centeredSphereChart_target]; trivial)

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

lemma sphereCoordFlux_divergence (p : Base) (x : _root_.OAI.Yau.Jets.Coord) :
    complexDivergence (sphereCoordFlux A f p) x =
      ((∑ i, fderiv ℝ (intrinsicRoundFlux A f p i) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  unfold complexDivergence
  apply Finset.sum_congr rfl
  intro i _
  exact seedCoordPartial_pullback _
    ((intrinsicRoundFlux_smooth A hA hs hp f hf p i).differentiable (by simp)) i x

lemma sphereChartTransition_divergence (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
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

theorem intrinsicWeightedChartOperator_transition (rho : Base → ℝ) (p q : Base) {x : _root_.OAI.Yau.Jets.Coord}
    (hx : x ∈ sphereChartTransitionDomain p q) :
    intrinsicWeightedChartOperator A rho f p (seedCoordEquiv x) =
      intrinsicWeightedChartOperator A rho f q (seedCoordEquiv (sphereChartTransition p q x)) := by
  have hd := sphereChartTransition_divergence A hA hs hp f hf p q hx
  rw [sphereCoordFlux_divergence A hA hs hp f hf,
    sphereCoordFlux_divergence A hA hs hp f hf] at hd
  have hdR : (∑ i, fderiv ℝ (intrinsicRoundFlux A f p i) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
      |(jacobian (sphereChartTransition p q) x).det| *
        ∑ i, fderiv ℝ (intrinsicRoundFlux A f q i) (seedCoordEquiv (sphereChartTransition p q x))
          (EuclideanSpace.basisFun (Fin 4) ℝ i) := by exact_mod_cast hd
  have hpoint := sphereChartTransition_point p q hx
  have hn := abs_ne_zero.mpr (sphereChartTransition_jacobian_ne_zero p q hx)
  unfold sphereChartCoordMap at hpoint
  simp only [intrinsicWeightedChartOperator,hdR,sphereChartTransition_round_density p q hx,
    hpoint,_root_.mul_inv_rev]
  calc
    _ = (rho ((extChartAt (𝓡 4) p).symm (seedCoordEquiv x)))⁻¹ *
        (roundChartDensity q (seedCoordEquiv (sphereChartTransition p q x)))⁻¹ *
        (|(jacobian (sphereChartTransition p q) x).det|⁻¹ *
          |(jacobian (sphereChartTransition p q) x).det|) *
          (∑ i, fderiv ℝ (intrinsicRoundFlux A f q i) (seedCoordEquiv (sphereChartTransition p q x))
            (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn,mul_one]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_GlobalSphereEquation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (lam : ℝ)
include hA hs hp hf

theorem intrinsic_global_equation_of_seed_exterior (K : Set Base)
    (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hseed : ∀ x, -intrinsicWeightedChartOperator A rho f seedPoint (seedCoordEquiv x) =
      lam*f (seedSphereFromCoord x))
    (hext : ∀ p z, (extChartAt (𝓡 4) p).symm z ∉ K →
      -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z) := by
  intro p z
  by_cases hz : (extChartAt (𝓡 4) p).symm z ∈ K
  · have hov : seedCoordEquiv.symm z ∈ sphereChartTransitionDomain p seedPoint := by
      simpa only [sphereChartTransitionDomain,sphereChartCoordMap,mem_preimage,
        seedCoordEquiv.apply_symm_apply] using hK hz
    have hi := intrinsicWeightedChartOperator_transition A hA hs hp f hf rho p seedPoint hov
    rw [seedCoordEquiv.apply_symm_apply] at hi
    rw [hi,hseed]
    have hpoint := sphereChartTransition_point p seedPoint hov
    simpa only [sphereChartCoordMap,seedSphereFromCoord,seedCoordEquiv.apply_symm_apply] using
      congrArg (fun y ↦ lam*f y) hpoint
  · exact hext p z hz

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix
open scoped RealInnerProductSpace
noncomputable section

lemma sphereTangentProjection_inner (x : Base) (v w : AmbientBase) :
    ⟪sphereTangentProjection x v,sphereTangentProjection x w⟫ +
      ⟪(x:AmbientBase),v⟫ * ⟪(x:AmbientBase),w⟫ = ⟪v,w⟫ := by
  simp only [sphereTangentProjection,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    sphere_radial_norm,one_pow,real_inner_comm v (x:AmbientBase)]
  ring

lemma intrinsicAmbientForm_reference (A : IntrinsicTensor) (x : Base)
    (hA : ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (v w : AmbientBase) : intrinsicAmbientForm A x v w = ⟪v,w⟫ := by
  have h := hA (sphereTangentProjection x v) (sphereTangentProjection x w)
    (sphereTangentProjection_orthogonal x v) (sphereTangentProjection_orthogonal x w)
  rw [sphereTangentProjection_restriction,sphereTangentProjection_restriction] at h
  rw [intrinsicAmbientForm_apply,h,sphereTangentProjection_inner]

lemma intrinsicAmbientMatrix_reference (A : IntrinsicTensor) (x : Base)
    (hA : ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) :
    intrinsicAmbientMatrix A x = 1 := by
  ext i j
  change intrinsicAmbientForm A x (EuclideanSpace.basisFun (Fin 5) ℝ i)
    (EuclideanSpace.basisFun (Fin 5) ℝ j) = _
  rw [intrinsicAmbientForm_reference A x hA]
  exact (EuclideanSpace.basisFun (Fin 5) ℝ).inner_eq_ite i j

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentTensor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst1
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst2
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst3
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst4
lemma sphereCotangentRepresentative_orthogonal (x : Base) (ell : SphereCotangent x) :
    ⟪(x:AmbientBase),sphereCotangentRepresentative x ell⟫ = 0 := by
  have h := sphere_derivative_radial_orthogonal x ((sphereRoundMusical x).symm ell)
  simpa [sphereCotangentRepresentative,PiLp.inner_apply,dotProduct,mul_comm] using h

lemma sphereCotangentRepresentative_unique (x : Base) (ell : SphereCotangent x)
    (v : AmbientBase) (hr : sphereCovectorRestriction x v = ell)
    (ho : ⟪(x:AmbientBase),v⟫ = 0) : sphereCotangentRepresentative x ell = v := by
  apply sub_eq_zero.mp
  apply sphereCovectorRestriction_separates x
  · rw [map_sub,sphereCotangentRepresentative_restriction,hr,sub_self]
  · rw [inner_sub_right,sphereCotangentRepresentative_orthogonal,ho,sub_self]

lemma sphereCotangentRepresentative_project (x : Base) (v : AmbientBase) :
    sphereCotangentRepresentative x (sphereCovectorRestriction x v) = sphereTangentProjection x v :=
  sphereCotangentRepresentative_unique x _ _ (sphereTangentProjection_restriction x v)
    (sphereTangentProjection_orthogonal x v)

lemma roundCotangentTensor_restriction (x : Base) (v w : AmbientBase) :
    roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) =
      ⟪sphereTangentProjection x v,sphereTangentProjection x w⟫ := by
  rw [roundCotangentTensor_apply,sphereCotangentRepresentative_project,sphereCotangentRepresentative_project]

lemma roundCotangentTensor_tangent (x : Base) (v w : AmbientBase)
    (hv : ⟪(x:AmbientBase),v⟫ = 0) (hw : ⟪(x:AmbientBase),w⟫ = 0) :
    roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫ := by
  simp [roundCotangentTensor_restriction,sphereTangentProjection,hv,hw]

lemma roundCotangentTensor_ambient (x : Base) : intrinsicAmbientMatrix roundCotangentTensor x = 1 :=
  intrinsicAmbientMatrix_reference _ x (roundCotangentTensor_tangent x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SpherePositiveMargins
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma intrinsic_sphere_positive_margin (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c > 0, ∀ x v, c*roundCotangentTensor x v v ≤ A x v v := by
  let B := fun x ↦ ambientMatrixForm (intrinsicAmbientMatrix A x)
  have hB : Continuous B := (ambientMatrixForm_smooth _ (intrinsicAmbientMatrix_smooth A hA)).continuous
  have hpos (x : Base) (v : AmbientBase) (hv : v ≠ 0) : 0 < B x v v :=
    ambientMatrixForm_pos _ (intrinsicAmbientMatrix_posDef A hs hp x) v hv
  have hc : Continuous (fun z : Base × AmbientBase ↦ B z.1 z.2 z.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:AmbientBase) 1)) _ hc.continuousOn
    (fun z hz ↦ hpos z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hb (x : Base) (v : AmbientBase) : c*‖v‖^2 ≤ B x v v := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (x,(‖v‖⁻¹:ℝ) • v)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
    simp only [map_smul,smul_apply,smul_eq_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
    have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*B x v v)) = B x v v := by field_simp
    rw [he] at hmul
    nlinarith
  refine ⟨c,hc0,?_⟩
  intro x v
  have hh := hb x (sphereCotangentRepresentative x v)
  rw [show B x = ambientMatrixForm (intrinsicAmbientMatrix A x) from rfl,
    intrinsicAmbientMatrix_pairing,sphereCotangentRepresentative_restriction,
    sphereCotangentRepresentative_orthogonal,zero_mul,add_zero] at hh
  simpa only [roundCotangentTensor_apply,real_inner_self_eq_norm_sq] using hh

lemma intrinsic_pair_positive_margin (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, (∀ x v, c*roundCotangentTensor x v v ≤ A x v v) ∧ ∀ x, c ≤ rho x := by
  obtain ⟨a,ha,hb⟩ := intrinsic_sphere_positive_margin A hA hs hp
  obtain ⟨r,hr0,_,_,hrb⟩ := compact_positive_bounds isCompact_univ rho hr.continuous.continuousOn
    (fun x _ ↦ hrp x)
  refine ⟨min a r,lt_min ha hr0,?_,fun x ↦ (min_le_right _ _).trans (hrb x (mem_univ _)).1⟩
  intro x v
  have hn : 0 ≤ roundCotangentTensor x v v := by
    rw [roundCotangentTensor_apply]; exact real_inner_self_nonneg
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hn).trans (hb x v)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartConformal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereRoundChartMatrix_inverse_conformal (p : Base) (y : BaseModel) :
    (sphereRoundChartMatrix p y)⁻¹ = ((4/(‖y‖^2+4))^2)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  let : Invertible ((4/(‖y‖^2+4))^2) := invertibleOfNonzero (by positivity)
  rw [sphereRoundChartMatrix_conformal,Matrix.inv_smul (A := (1 : Matrix (Fin 4) (Fin 4) ℝ)) ((4/(‖y‖^2+4))^2) (by simp)]
  simp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Bundle Manifold Matrix Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst1
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst2
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst3
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst4
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst5
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst6
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst7
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst8
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst9
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst10
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst11
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst12
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst13
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst14
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst15
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst16
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst17
attribute [local instance] OAI.Yau.Target.intrinsicRoundPerturbationLocalInst18
lemma roundTensorPerturbation_smooth (alpha : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ alpha) :
    IntrinsicTensorSmooth (roundTensorPerturbation alpha) :=
  ha.smul_section roundCotangentTensor_smooth

lemma intrinsicSphereChartTensor_add (A B : IntrinsicTensor) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor (fun x ↦ A x+B x) p z =
      intrinsicSphereChartTensor A p z+intrinsicSphereChartTensor B p z := by
  ext i j
  rfl

lemma roundCotangentTensor_chart (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor roundCotangentTensor p z = (sphereRoundChartMatrix p z)⁻¹ := by
  rw [intrinsicSphereChartTensor_eq]
  have he : intrinsicAmbientMatrix roundCotangentTensor = fun _ ↦ 1 := funext roundCotangentTensor_ambient
  rw [he]
  have hinv := Matrix.mul_nonsing_inv (sphereRoundChartMatrix p z)
    (isUnit_iff_ne_zero.mpr (sphereRoundChartMatrix_posDef p
      (by rw [centeredSphereChart_target]; trivial)).det_pos.ne')
  simp only [sphereChartTensor,frameContravariant,Matrix.mul_one]
  simp only [Matrix.mul_assoc] at *
  rw [← Matrix.mul_assoc (sphereChartFrame p z).transpose (sphereChartFrame p z)]
  change (sphereRoundChartMatrix p z)⁻¹ * (sphereRoundChartMatrix p z * (sphereRoundChartMatrix p z)⁻¹) = _
  rw [hinv,Matrix.mul_one]

lemma roundTensorPerturbation_chart (alpha : Base → ℝ) (p : Base) (z : BaseModel) :
    intrinsicSphereChartTensor (roundTensorPerturbation alpha) p z =
      alpha ((extChartAt (𝓡 4) p).symm z) • (sphereRoundChartMatrix p z)⁻¹ := by
  rw [← roundCotangentTensor_chart]
  ext i j
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PositiveSphereCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst3
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst4
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst1
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst2
local instance positiveSphereCorrectionLocalInst5_rf4e1ae_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst6_rf4e1ae_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst7
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst8
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst9
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst10
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst11
local instance positiveSphereCorrectionLocalInst12_rf4e1ae_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst13
local instance positiveSphereCorrectionLocalInst14_rf4e1ae_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst15
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst16
lemma round_perturbed_pair_positive (A : IntrinsicTensor) (rho alpha beta : Base → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hA : ∀ x v, c*roundCotangentTensor x v v ≤ A x v v)
    (hr : ∀ x, c ≤ rho x) (ha : ∀ x, |alpha x| < c) (hb : ∀ x, |beta x| < c) :
    (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v) ∧
    ∀ x, 0 < rho x+beta x := by
  constructor
  · intro x v hv
    have hp := roundCotangentTensor_pos x v hv
    have hlow := hA x v
    have hs := (abs_lt.mp (ha x)).1
    have hmul : 0 < (c+alpha x)*roundCotangentTensor x v v := mul_pos (by linarith) hp
    change 0 < A x v v+alpha x*roundCotangentTensor x v v
    nlinarith
  · intro x
    by_cases hbeta : 0 ≤ beta x
    · exact add_pos_of_pos_of_nonneg (hc.trans_le (hr x)) hbeta
    have hs := (abs_lt.mp (hb x)).1
    have := hr x
    linarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCorrectionResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

lemma intrinsicCorrectionResidual_divergence (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (lam : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    intrinsicCorrectionResidual A rho lam
      (fun z ↦ f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z))) x =
      (-(roundChartDensity seedPoint (seedCoordEquiv x))⁻¹ *
        (∑ i, fderiv ℝ (intrinsicRoundFlux A f seedPoint i) (seedCoordEquiv x)
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) -
        lam*seedCoordDensity rho x*f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℝ) := by
  rw [intrinsicCorrectionResidual,realSourceResidual,
    intrinsicSeedCoordOperator A hAs hs hp rho hrp f hf]
  have hn : seedCoordDensity rho x ≠ 0 := (hrp _).ne'
  simp only [intrinsicWeightedChartOperator,seedCoordDensity,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv]
  have hn' : (rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ) ≠ 0 := by
    exact_mod_cast hn
  field_simp
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoordinateCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
variable {n : ℕ}

theorem coordDiv_mul {u : Coord n → ℝ} {V : Coord n → Coord n} {x : Coord n}
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    coordDiv (fun y i ↦ u y * V y i) x =
      u x * coordDiv V x + pairing u V x := by
  unfold coordDiv pairing coordPartial
  simp_rw [fderiv_fun_mul hu (hV _)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedDiv_mul {gamma u : Coord n → ℝ} {V : Coord n → Coord n}
    {x : Coord n} (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    weightedDiv gamma (fun y i ↦ u y * V y i) x =
      u x * weightedDiv gamma V x + pairing u V x := by
  have heq : (fun y i ↦ gamma y * (u y * V y i)) =
      (fun y i ↦ u y * (gamma y * V y i)) := by
    funext y i
    ring
  unfold weightedDiv
  rw [heq, coordDiv_mul (V := fun y i ↦ gamma y * V y i) hu (fun i ↦ hg.mul (hV i))]
  have hp : pairing u (fun y i ↦ gamma y * V y i) x = gamma x * pairing u V x := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp]
  field_simp

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundCoordinateGradient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundCoordFactor_smooth : ContDiff ℝ ∞ roundCoordFactor := by
  unfold roundCoordFactor
  exact ((((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const).div_const 4).pow 2

lemma roundCoordGradient_smooth (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (roundCoordGradient u) := by
  apply contDiff_pi.mpr
  intro i
  exact roundCoordFactor_smooth.mul ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicRealCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

lemma intrinsicRealCorrectionResidual_divergence (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (lam : ℝ) (x : Yau.Jets.Coord) :
    intrinsicRealCorrectionResidual A rho lam
      (fun z ↦ f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z))) x =
      -(roundCoordDensity x)⁻¹ *
        (∑ i, fderiv ℝ (intrinsicRoundFlux A f seedPoint i) (seedCoordEquiv x)
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) -
        lam*seedCoordDensity rho x*f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) := by
  exact congrArg Complex.re (intrinsicCorrectionResidual_divergence A hAs hs hp rho hrp f hf lam x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundPerturbationFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seed_real_partial_pullback (f : Base → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    fderiv ℝ (fun z ↦ f (seedSphereFromCoord z)) x (Pi.single i 1) =
      fderiv ℝ (f ∘ (extChartAt (𝓡 4) seedPoint).symm) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  change fderiv ℝ ((f ∘ (extChartAt (𝓡 4) seedPoint).symm) ∘ seedCoordEquiv) x _ = _
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma roundTensorPerturbation_seed_flux (a f : Base → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    intrinsicRoundFlux (roundTensorPerturbation a) f seedPoint i (seedCoordEquiv x) =
      roundCoordDensity x * (a (seedSphereFromCoord x) *
        roundCoordGradient (fun z ↦ f (seedSphereFromCoord z)) x i) := by
  rw [intrinsicRoundFlux,roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul]
  rw [roundCoordGradient,seed_real_partial_pullback]
  simp [roundCoordDensity,seedSphereFromCoord,mul_assoc]

lemma roundTensorPerturbation_seed_divergence (a f : Base → ℝ) (x : Yau.Jets.Coord) :
    (roundCoordDensity x)⁻¹ *
      (∑ i, fderiv ℝ (intrinsicRoundFlux (roundTensorPerturbation a) f seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
    Yau.weightedDiv roundCoordDensity (fun z i ↦ a (seedSphereFromCoord z) *
      roundCoordGradient (fun w ↦ f (seedSphereFromCoord w)) z i) x := by
  unfold Yau.weightedDiv Yau.coordDiv Yau.coordPartial
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun z ↦ roundCoordDensity z * (a (seedSphereFromCoord z) *
      roundCoordGradient (fun w ↦ f (seedSphereFromCoord w)) z i)) =
      (intrinsicRoundFlux (roundTensorPerturbation a) f seedPoint i) ∘ seedCoordEquiv := by
    funext z
    exact (roundTensorPerturbation_seed_flux a f z i).symm
  rw [he,seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicCorrectedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance intrinsicCorrectedChartLocalInst1_rf4e1ae_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst2_rf4e1ae_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst3_rf4e1ae_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst4_rf4e1ae_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst5_rf4e1ae_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst6_rf4e1ae_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst7
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst8
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst9
local instance intrinsicCorrectedChartLocalInst10_rf4e1ae_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst11
local instance intrinsicCorrectedChartLocalInst12_rf4e1ae_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicCorrectedChartLocalInst13_rf4e1ae_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicCorrectedChartLocalInst14_rf4e1ae_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance intrinsicCorrectedChartLocalInst15_rf4e1ae_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicCorrectedChartLocalInst16_rf4e1ae_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
lemma intrinsicRoundFlux_add (A B : IntrinsicTensor) (f : Base → ℝ) (p : Base) (i : Fin 4) :
    intrinsicRoundFlux (fun x ↦ A x+B x) f p i =
      fun z ↦ intrinsicRoundFlux A f p i z+intrinsicRoundFlux B f p i z := by
  funext z
  simp only [intrinsicRoundFlux,intrinsicSphereChartTensor_add,Matrix.add_apply,
    add_mul,Finset.sum_add_distrib,mul_add]

theorem corrected_seed_chart_equation (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ) (a b : Base → ℝ)
    (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation a x))
    (hnewSym : ∀ x v w, (A x+roundTensorPerturbation a x) v w = (A x+roundTensorPerturbation a x) w v)
    (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation a x) v v)
    (hrnew : ∀ x, 0 < rho x+b x)
    (heq : ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) =
      intrinsicRealCorrectionResidual A rho lam (fun z ↦ u (seedSphereFromCoord z)) x) :
    ∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation a p)
      (fun p ↦ rho p+b p) u seedPoint (seedCoordEquiv x) = lam*u (seedSphereFromCoord x) := by
  intro x
  let B := roundTensorPerturbation a
  have hdiff (i : Fin 4) : Differentiable ℝ (intrinsicRoundFlux B u seedPoint i) := by
    have hn := intrinsicRoundFlux_smooth (fun p ↦ A p+B p) hnew hnewSym hnewPos u hu seedPoint i
    have ho := intrinsicRoundFlux_smooth A hAs hs hp u hu seedPoint i
    have he : intrinsicRoundFlux B u seedPoint i = fun z ↦
        intrinsicRoundFlux (fun p ↦ A p+B p) u seedPoint i z-intrinsicRoundFlux A u seedPoint i z := by
      funext z
      rw [intrinsicRoundFlux_add]
      ring
    rw [he]
    exact (hn.sub ho).differentiable (by simp)
  have hsum : (∑ i, fderiv ℝ (intrinsicRoundFlux (fun p ↦ A p+B p) u seedPoint i)
      (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
      (∑ i, fderiv ℝ (intrinsicRoundFlux A u seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) +
      (∑ i, fderiv ℝ (intrinsicRoundFlux B u seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
    simp only [intrinsicRoundFlux_add]
    simp_rw [fderiv_fun_add
      ((intrinsicRoundFlux_smooth A hAs hs hp u hu seedPoint _).differentiable (by simp) _)
      (hdiff _ _),add_apply,Finset.sum_add_distrib]
  have h := heq x
  rw [← roundTensorPerturbation_seed_divergence] at h
  have hres := intrinsicRealCorrectionResidual_divergence A hAs hs hp rho hrp u hu lam x
  change intrinsicRealCorrectionResidual A rho lam (fun z ↦ u (seedSphereFromCoord z)) x = _ at hres
  rw [hres] at h
  change -((rho (seedSphereFromCoord x)+b (seedSphereFromCoord x))⁻¹ *
    (roundCoordDensity x)⁻¹ *
      (∑ i, fderiv ℝ (intrinsicRoundFlux (fun p ↦ A p+B p) u seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i))) = _
  rw [hsum]
  have hd : rho (seedSphereFromCoord x)+b (seedSphereFromCoord x) ≠ 0 := (hrnew _).ne'
  change _ + lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) =
    _ - lam*rho (seedSphereFromCoord x)*u (seedSphereFromCoord x) at h
  apply (mul_left_cancel₀ hd)
  field_simp
  simp only [div_eq_mul_inv]
  dsimp only [B] at *
  nlinarith only [h]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma matrixContravariant_add (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixContravariant (A+B) = matrixContravariant A+matrixContravariant B := by
  ext α i
  simp [matrixContravariant,add_smul,Finset.sum_add_distrib]

lemma matrixContravariant_entry_sum (A : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixContravariant A = ∑ i, ∑ j, coefficientEntryLinear i j (A i j) := rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientIncrementBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicChartCoefficient_increment (A B : IntrinsicTensor) (rho b : Base → ℝ)
    (p : Base) (z : BaseModel) :
    intrinsicChartCoefficient (fun x ↦ A x+B x) (fun x ↦ rho x+b x) p z -
      intrinsicChartCoefficient A rho p z = intrinsicChartCoefficient B b p z := by
  apply Prod.ext
  · simp only [intrinsicChartCoefficient,Prod.fst_sub,intrinsicSphereChartTensor_add,
      matrixContravariant_add,add_sub_cancel_left]
  · simp [intrinsicChartCoefficient]

lemma seed_scalar_pullback_smooth (b : Base → ℝ)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun x ↦ b (seedSphereFromCoord x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (smooth_inverse_chart_comp b hb seedPoint
    (by rw [centeredSphereChart_target]; trivial)).comp x seedCoordEquiv.contDiff.contDiffAt

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SpherePreservingEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsicWeightedChartOperator_coefficients_eq (A B : IntrinsicTensor)
    (rho sigma u : Base → ℝ) (p : Base) (z : BaseModel)
    (hA : ∀ᶠ x in 𝓝 ((extChartAt (𝓡 4) p).symm z), A x = B x)
    (hr : rho =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] sigma) :
    intrinsicWeightedChartOperator A rho u p z = intrinsicWeightedChartOperator B sigma u p z := by
  have he := (continuousAt_extChartAt_symm''
    (by rw [centeredSphereChart_target]; trivial : z ∈ (extChartAt (𝓡 4) p).target)).eventually hA
  have hf (i : Fin 4) : intrinsicRoundFlux A u p i =ᶠ[𝓝 z] intrinsicRoundFlux B u p i := by
    filter_upwards [he] with y hy
    simp only [intrinsicRoundFlux,intrinsicSphereChartTensor,hy]
  simp only [intrinsicWeightedChartOperator,hr.eq_of_nhds]
  congr 2
  funext i
  rw [(hf i).fderiv_eq]

lemma intrinsic_eigenfunction_correction_residual_zero
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho u : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) :
    ∀ x, intrinsicRealCorrectionResidual A rho lam (fun y ↦ u (seedSphereFromCoord y)) x = 0 := by
  intro x
  have hres := intrinsicRealCorrectionResidual_divergence A hA hs hp rho hrp u hu lam x
  change intrinsicRealCorrectionResidual A rho lam (fun y ↦ u (seedSphereFromCoord y)) x = _ at hres
  rw [hres]
  have hn : rho (seedSphereFromCoord x) ≠ 0 := (hrp _).ne'
  have h := congrArg (fun v : ℝ ↦ rho (seedSphereFromCoord x)*v) (he seedPoint (seedCoordEquiv x))
  change rho (seedSphereFromCoord x)*
    (-((rho (seedSphereFromCoord x))⁻¹*(roundCoordDensity x)⁻¹*
      (∑ i, fderiv ℝ (intrinsicRoundFlux A u seedPoint i) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i)))) =
      rho (seedSphereFromCoord x)*(lam*u (seedSphereFromCoord x)) at h
  simp only [← mul_assoc,mul_neg,mul_inv_cancel₀ hn,one_mul] at h
  change -(roundCoordDensity x)⁻¹ * _ - lam*rho (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0
  nlinarith only [h]

lemma round_preserving_cancellation_smul (u a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (lam t : ℝ)
    (he : ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0) :
    ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ (t*a (seedSphereFromCoord y))*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*(t*b (seedSphereFromCoord x))*u (seedSphereFromCoord x) = 0 := by
  intro x
  have hav := seed_scalar_pullback_smooth a ha
  have hV := roundCoordGradient_smooth _ (seed_scalar_pullback_smooth u hu)
  have hmul := Yau.weightedDiv_mul (gamma := roundCoordDensity) (u := fun _ ↦ t)
    (V := fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i)
    (x := x) (roundCoordDensity_smooth.differentiable (by simp) x) (roundCoordDensity_pos x).ne'
    (differentiableAt_const t) (fun i ↦ (hav.mul ((contDiff_pi.mp hV) i)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
  simp only [Yau.pairing,Yau.coordPartial,fderiv_fun_const,Pi.zero_apply,zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero] at hmul
  simp only [mul_assoc] at ⊢ hmul
  rw [hmul]
  have ht := congrArg (fun q : ℝ ↦ t*q) (he x)
  nlinarith only [ht]

theorem sphere_equation_preserved_by_round_cancellation
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho u a b : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z))
    (hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation a x))
    (hnewSym : ∀ x v w, (A x+roundTensorPerturbation a x) v w = (A x+roundTensorPerturbation a x) w v)
    (hnewPos : ∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation a x) v v)
    (hrnew : ∀ x, 0 < rho x+b x)
    (hsa : tsupport a ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hsb : tsupport b ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hcancel : ∀ x, Yau.weightedDiv roundCoordDensity
      (fun y i ↦ a (seedSphereFromCoord y)*roundCoordGradient (fun z ↦ u (seedSphereFromCoord z)) y i) x +
      lam*b (seedSphereFromCoord x)*u (seedSphereFromCoord x) = 0) :
    ∀ p z, -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation a x)
      (fun x ↦ rho x+b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z) := by
  have hres := intrinsic_eigenfunction_correction_residual_zero A hA hs hp rho u hrp hu lam he
  have hseed := corrected_seed_chart_equation A hA hs hp rho hrp u hu lam a b
    hnew hnewSym hnewPos hrnew (fun x ↦ (hcancel x).trans (hres x).symm)
  apply intrinsic_global_equation_of_seed_exterior _ hnew hnewSym hnewPos _ u hu lam
    (tsupport a ∪ tsupport b) (union_subset hsa hsb) hseed
  intro p z hz
  have ha0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (Or.inl h))
  have hb0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (Or.inr h))
  have hAe : ∀ᶠ x in 𝓝 ((extChartAt (𝓡 4) p).symm z),
      A x+roundTensorPerturbation a x = A x := by
    filter_upwards [ha0] with x hx
    simp [roundTensorPerturbation,hx]
  have hre : (fun x ↦ rho x+b x) =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] rho := by
    filter_upwards [hb0] with x hx
    simp [hx]
  rw [intrinsicWeightedChartOperator_coefficients_eq _ A _ rho u p z hAe hre]
  exact he p z

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SupportedCoefficientChartBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma roundTensorPerturbation_any_entry (a : Base → ℝ) (p : Base) (x : Yau.Jets.Coord) (j k : Fin 4) :
    intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x) j k =
      if j=k then roundCoordFactor x*a (sphereChartCoordMap p x) else 0 := by
  rw [roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp [Matrix.one_apply,sphereChartCoordMap,mul_comm]

lemma round_increment_any_entry_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (p : Base) (j k : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x) j k) := by
  simp_rw [roundTensorPerturbation_any_entry]
  split_ifs
  · exact roundCoordFactor_smooth.mul (ha.comp (sphereChartCoordMap_smooth p)).contDiff
  · exact contDiff_const

lemma intrinsic_any_increment_pullback_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicChartCoefficient (roundTensorPerturbation a) b p (seedCoordEquiv x)) := by
  apply ContDiff.prodMk _ (hb.comp (sphereChartCoordMap_smooth p)).contDiff
  change ContDiff ℝ ∞ (fun x ↦ matrixContravariant
    (intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv x)))
  simp_rw [matrixContravariant_entry_sum]
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦
    (round_increment_any_entry_smooth a ha p j k).smul contDiff_const))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SupportedFiniteAtlasBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma sphereAtlasCore_compact : IsCompact sphereAtlasCore :=
  (isCompact_closedBall _ _).image seedCoordEquiv.continuous

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientDistanceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsic_coefficient_chart_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (p : Base) :
    ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p) :=
  contDiff_iff_contDiffAt.mpr (fun z ↦ intrinsicChartCoefficient_smoothAt A hA hs hp rho hr p
    (by rw [centeredSphereChart_target]; trivial))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmallRoundPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma intrinsic_round_increment_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    (p : Base) : ContDiff ℝ ∞ (intrinsicChartCoefficient (roundTensorPerturbation a) b p) := by
  have h := (intrinsic_any_increment_pullback_smooth a b ha hb p).comp seedCoordEquiv.symm.contDiff
  simpa only [Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using h

lemma intrinsic_round_increment_smul (a b : Base → ℝ) (t : ℝ) (p : Base) (z : BaseModel) :
    intrinsicChartCoefficient (roundTensorPerturbation (fun x ↦ t*a x)) (fun x ↦ t*b x) p z =
      t • intrinsicChartCoefficient (roundTensorPerturbation a) b p z := by
  apply Prod.ext
  · change matrixContravariant (intrinsicSphereChartTensor
        (roundTensorPerturbation (fun x ↦ t*a x)) p z) =
      t • matrixContravariant (intrinsicSphereChartTensor (roundTensorPerturbation a) p z)
    simp only [roundTensorPerturbation_chart,matrixContravariant,Matrix.smul_apply,
      smul_eq_mul,Finset.smul_sum,smul_smul,mul_assoc]
  · rfl

lemma sphereCoefficientDistance_round_smul (P : Finset Base) (J : ℕ)
    (A : IntrinsicTensor) (rho a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (t : ℝ) :
    sphereCoefficientDistance P J A rho
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) =
      |t| * finiteChartDerivativeSize P sphereAtlasCore J
        (intrinsicChartCoefficient (roundTensorPerturbation a) b) := by
  simp only [sphereCoefficientDistance,intrinsicChartCoefficient_increment,intrinsic_round_increment_smul]
  simpa only [Real.norm_eq_abs] using finiteChartDerivativeSize_smul P sphereAtlasCore_compact J t
    (intrinsicChartCoefficient (roundTensorPerturbation a) b)
    (fun p _ ↦ intrinsic_round_increment_smooth a b ha hb p)

theorem small_round_perturbation_in_finite_atlas
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) (P : Finset Base) (J : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ t : ℝ, |t| < delta →
      IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
      (∀ x v w, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v w =
        (A x+roundTensorPerturbation (fun y ↦ t*a y) x) w v) ∧
      (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) v v) ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
      (∀ x, 0 < rho x+t*b x) ∧
      sphereCoefficientDistance P J A rho
        (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) < eps := by
  obtain ⟨c,hc,hAm,hrm⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  obtain ⟨Ba,hBa⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuous.continuousOn
  obtain ⟨Bb,hBb⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuous.continuousOn
  let B : ℝ := max 0 (max Ba Bb)+1
  have hB : 0 < B := by dsimp [B]; have := le_max_left (0:ℝ) (max Ba Bb); linarith
  have hab (x : Base) : |a x| ≤ B := by
    have h := hBa x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    have hh : Ba ≤ max 0 (max Ba Bb) := (le_max_left Ba Bb).trans (le_max_right _ _)
    dsimp [B] <;> linarith
  have hbb (x : Base) : |b x| ≤ B := by
    have h := hBb x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    have hh : Bb ≤ max 0 (max Ba Bb) := (le_max_right Ba Bb).trans (le_max_right _ _)
    dsimp [B] <;> linarith
  let C := finiteChartDerivativeSize P sphereAtlasCore J
    (intrinsicChartCoefficient (roundTensorPerturbation a) b)
  have hC : 0 ≤ C := finiteChartDerivativeSize_nonneg P sphereAtlasCore_compact J _
    (fun p _ ↦ intrinsic_round_increment_smooth a b ha hb p)
  refine ⟨min (c/B) (eps/(C+1)),lt_min (div_pos hc hB) (div_pos heps (by linarith)),?_⟩
  intro t ht
  have htB : |t| * B < c := (lt_div_iff₀ hB).mp (ht.trans_le (min_le_left _ _))
  have htC : |t| * (C+1) < eps := (lt_div_iff₀ (by linarith : 0 < C+1)).mp
    (ht.trans_le (min_le_right _ _))
  obtain ⟨hpos,hden⟩ := round_perturbed_pair_positive A rho (fun x ↦ t*a x) (fun x ↦ t*b x)
    hc hAm hrm
    (fun x ↦ by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hab x) (abs_nonneg t)).trans_lt htB)
    (fun x ↦ by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hbb x) (abs_nonneg t)).trans_lt htB)
  refine ⟨hA.add_section (roundTensorPerturbation_smooth _ (contMDiff_const.mul ha)),?_,hpos,
    hr.add (contMDiff_const.mul hb),hden,?_⟩
  · intro x v w
    change A x v w+(t*a x)*roundCotangentTensor x v w = A x w v+(t*a x)*roundCotangentTensor x w v
    rw [hs,roundCotangentTensor_symm]
  · rw [sphereCoefficientDistance_round_smul P J A rho a b ha hb t]
    change |t| * C < eps
    nlinarith [abs_nonneg t]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem exists_sphere_simplicity_perturbation
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hune : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) (r : ℝ) (hradius : 0 < r) :
    ∃ (Q : Set Yau.Jets.Coord) (a b : Base → ℝ),
      IsCompact Q ∧ Q ⊆ seedCoordPatch r ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
      tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
      IsCompact (seedSphereFromCoord '' Q) ∧ seedSphereFromCoord '' Q ⊆ seedSpherePatch r ∧
      (∀ t x, x ∉ seedSphereFromCoord '' Q →
        A x+roundTensorPerturbation (fun y ↦ t*a y) x = A x ∧ rho x+t*b x = rho x) ∧
      ∀ (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps → ∃ delta > 0,
        ∀ t : ℝ, |t| < delta → t ≠ 0 →
          IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) ∧
          (∀ x alpha beta, (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha beta =
            (A x+roundTensorPerturbation (fun y ↦ t*a y) x) beta alpha) ∧
          (∀ x alpha, alpha ≠ 0 → 0 < (A x+roundTensorPerturbation (fun y ↦ t*a y) x) alpha alpha) ∧
          ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+t*b x) ∧
          (∀ x, 0 < rho x+t*b x) ∧
          sphereCoefficientDistance P J A rho
            (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x) (fun x ↦ rho x+t*b x) < eps ∧
          (∀ p z, -intrinsicWeightedChartOperator
            (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
            (fun x ↦ rho x+t*b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z)) ∧
          ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
            (∀ p z, -intrinsicWeightedChartOperator
              (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
              (fun x ↦ rho x+t*b x) v p z = lam*v ((extChartAt (𝓡 4) p).symm z)) →
            ∃ c : ℝ, v = c • u := by
  classical
  obtain ⟨Q,zeta,a,b,hQ,hQP,_,_,_,_,ha,hb,haQ,hbQ,_,_,hcancel,_,hkernel⟩ :=
    exists_sphere_simplicity_kernel_form A hA hs hp rho hr hrp u hu hune lam hlam heu r hradius
  have hQsource : seedSphereFromCoord '' Q ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro x ⟨y,_,rfl⟩
    exact seedSphereFromCoord_source y
  obtain ⟨dpre,hdpre,hpre⟩ := small_round_perturbation_in_finite_atlas A hA hs hp rho hr hrp
    a b ha hb ∅ 0 (by norm_num : (0:ℝ)<1)
  have hpres (t : ℝ) (ht : |t| < dpre) : ∀ p z, -intrinsicWeightedChartOperator
      (fun x ↦ A x+roundTensorPerturbation (fun y ↦ t*a y) x)
      (fun x ↦ rho x+t*b x) u p z = lam*u ((extChartAt (𝓡 4) p).symm z) := by
    obtain ⟨h1,h2,h3,_,h5,_⟩ := hpre t ht
    exact sphere_equation_preserved_by_round_cancellation A hA hs hp rho u
      (fun x ↦ t*a x) (fun x ↦ t*b x) hrp hu lam heu h1 h2 h3 h5
      (tsupport_mul_subset_right.trans (haQ.trans hQsource))
      (tsupport_mul_subset_right.trans (hbQ.trans hQsource))
      (round_preserving_cancellation_smul u a b hu ha lam t hcancel)
  obtain ⟨ds,hds,hsimple⟩ := sphere_affine_kernel_implies_simplicity A hA hs hp rho hr hrp
    a b ha hb lam u hu hune hQ haQ hbQ (fun f hf hef ↦ (hkernel f hf hef).mp) dpre hdpre hpres
  refine ⟨Q,a,b,hQ,hQP,ha,hb,haQ,hbQ,hQ.image seedSphereFromCoord_continuous,?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨seedCoordEquiv y,hQP hy,rfl⟩
  · intro t x hx
    have ha0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (haQ h))
    have hb0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hbQ h))
    simp [roundTensorPerturbation,ha0,hb0]
  · intro P J eps heps
    obtain ⟨dn,hdn,hnorm⟩ := small_round_perturbation_in_finite_atlas A hA hs hp rho hr hrp
      a b ha hb P J heps
    refine ⟨min dn (min dpre ds),lt_min hdn (lt_min hdpre hds),?_⟩
    intro t ht htne
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hnorm t (ht.trans_le (min_le_left _ _))
    refine ⟨h1,h2,h3,h4,h5,h6,hpres t (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))),?_⟩
    exact hsimple t (ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))) htne

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

lemma coefficient_firstJet_dist_le
    (c d : BaseModel → CoefficientPoint BaseModel)
    (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) (x : BaseModel)
    {eta : ℝ} (h0 : ‖d x-c x‖ ≤ eta)
    (h1 : ‖fderiv ℝ (fun y ↦ d y-c y) x‖ ≤ eta) :
    dist ((d x,fderiv ℝ d x) : CoefficientFirstJet BaseModel)
      (c x,fderiv ℝ c x) ≤ eta := by
  rw [Prod.dist_eq]
  apply max_le
  · simpa only [dist_eq_norm] using h0
  · rw [fderiv_fun_sub (hd.differentiable (by simp) x) (hc.differentiable (by simp) x)] at h1
    simpa only [dist_eq_norm] using h1

lemma coefficient_compact_strict_margin
    (c : BaseModel → CoefficientPoint BaseModel) (hc : ContDiff ℝ ∞ c)
    {r delta : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ z ∈ closedBall (0 : BaseModel) r,
      dist ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) (roundCoefficientJet z) < delta) :
    ∃ eta > 0, ∀ z ∈ closedBall (0 : BaseModel) r,
      dist ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) (roundCoefficientJet z)+eta < delta := by
  let f : BaseModel → ℝ := fun z ↦
    dist ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) (roundCoefficientJet z)
  have hf : Continuous f :=
    (hc.continuous.prodMk (hc.continuous_fderiv (by simp))).dist roundCoefficientJet_continuous
  obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall (0 : BaseModel) r).exists_isMaxOn
    ⟨0,mem_closedBall_self hr⟩ hf.continuousOn
  refine ⟨(delta-f z)/2,by have := hclose z hz; change f z < delta at this; linarith,?_⟩
  intro y hy
  have hle : f y ≤ f z := hmax hy
  have hlt := hclose z hz
  change f z < delta at hlt
  change f y+(delta-f z)/2 < delta
  linarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmallRoundComparisonNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem small_round_perturbation_in_comparison_neighborhood
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (a b : Base → ℝ) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) {r delta : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta) :
    ∃ eta > 0, ∀ t : ℝ, |t| < eta → ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient (fun x ↦ d.tensor x+roundTensorPerturbation (fun z ↦ t*a z) x)
        (fun x ↦ d.density x+t*b x) seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient (fun x ↦ d.tensor x+roundTensorPerturbation (fun z ↦ t*a z) x)
          (fun x ↦ d.density x+t*b x) seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta := by
  let c := intrinsicChartCoefficient d.tensor d.density seedPoint
  let f := intrinsicChartCoefficient (roundTensorPerturbation a) b seedPoint
  have hc : ContDiff ℝ ∞ c := intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd seedPoint
  have hf : ContDiff ℝ ∞ f := intrinsic_round_increment_smooth a b ha hb seedPoint
  obtain ⟨eps,heps,hmargin⟩ := coefficient_compact_strict_margin c hc hr hclose
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : BaseModel) r).exists_bound_of_continuousOn
    (hf.continuous.prodMk (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).continuousOn
  let C : ℝ := max B 0+1
  have hC : 0 < C := by dsimp [C]; have := le_max_right B 0; linarith
  have hBC : B ≤ C := by dsimp [C]; have := le_max_left B 0; linarith
  refine ⟨eps/C,div_pos heps hC,?_⟩
  intro t ht y hy
  let c' : BaseModel → CoefficientPoint BaseModel := fun z ↦ c z+t • f z
  have hc' : ContDiff ℝ ∞ c' := hc.add (hf.const_smul t)
  have hid : intrinsicChartCoefficient (fun x ↦ d.tensor x+roundTensorPerturbation (fun z ↦ t*a z) x)
      (fun x ↦ d.density x+t*b x) seedPoint = c' := by
    funext z
    have h := intrinsicChartCoefficient_increment d.tensor (roundTensorPerturbation (fun z ↦ t*a z))
      d.density (fun z ↦ t*b z) seedPoint z
    rw [intrinsic_round_increment_smul] at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  rw [hid]
  have hnorm : ‖(f y,fderiv ℝ f y)‖ ≤ C := (hB y hy).trans hBC
  have h0 : ‖f y‖ ≤ C := (le_max_left _ _).trans hnorm
  have h1 : ‖fderiv ℝ f y‖ ≤ C := (le_max_right _ _).trans hnorm
  have hdiff : (fun z ↦ c' z-c z) = fun z ↦ t • f z := by funext z; dsimp [c']; abel
  have hj := coefficient_firstJet_dist_le c c' hc hc' y
    (show ‖c' y-c y‖ ≤ |t| *C by
      change ‖(fun z ↦ c' z-c z) y‖ ≤ _
      rw [hdiff,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h0 (abs_nonneg t))
    (show ‖fderiv ℝ (fun z ↦ c' z-c z) y‖ ≤ |t| *C by
      rw [hdiff,fderiv_fun_const_smul (hf.differentiable (by simp) y)]
      exact (ContinuousLinearMap.opNorm_smul_le t (fderiv ℝ f y)).trans
        (by simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left h1 (abs_nonneg t)))
  have htC := (lt_div_iff₀ hC).mp ht
  exact (dist_triangle _ ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) _).trans_lt
    (by have hm := hmargin y hy; linarith)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSimplicityInNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_simplicity_in_comparison_neighborhood_oai
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    {r delta : ℝ} (hr : 0 < r)
    (hclose : ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta)
    (K : Set Base) (hK : IsCompact K) (hKP : K ⊆ seedSpherePatch r)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
      d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫)
    (hrho : ∀ x ∉ K, d.density x=1)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
      lam*u ((extChartAt (𝓡 4) p).symm y))
    (P : Finset Base) (J : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density < eps ∧
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient b.tensor b.density seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient b.tensor b.density seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < delta) ∧
      ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
        (∀ x ∉ K', ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
        (∀ x ∉ K', b.density x=1) ∧
        (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density u p y =
          lam*u ((extChartAt (𝓡 4) p).symm y)) ∧
        (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
          (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
            lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) := by
  obtain ⟨Q,a,b,hQ,hQP,ha,hb,haQ,hbQ,himage,himageP,hext,H⟩ :=
    exists_sphere_simplicity_perturbation d.tensor d.smooth d.symm d.pos d.density hd d.positive
      u hu hu0 lam hlam he r hr
  obtain ⟨eta,heta,Heta⟩ := small_round_perturbation_in_comparison_neighborhood d hd a b ha hb hr.le hclose
  obtain ⟨ds,hds,Hds⟩ := H P J eps heps
  let t : ℝ := min eta ds/2
  have ht : 0 < t := by dsimp [t] <;> positivity
  have hteta : |t| < eta := by rw [abs_of_pos ht]; have := min_le_left eta ds; dsimp [t]; linarith
  have htds : |t| < ds := by rw [abs_of_pos ht]; have := min_le_right eta ds; dsimp [t]; linarith
  obtain ⟨h1,h2,h3,h4,h5,h6,he',hsimple⟩ := Hds t htds ht.ne'
  let d' : SphereEnergyData := ⟨_,h1,h2,h3,_,h4.continuous,h5⟩
  refine ⟨d',h4,h6,Heta t hteta,K ∪ seedSphereFromCoord '' Q,
    hK.union himage,subset_union_left,union_subset hKP himageP,?_,?_,he',hsimple⟩
  · intro x hx v w hv hw
    change (d.tensor x+roundTensorPerturbation (fun y ↦ t*a y) x) _ _ = _
    rw [(hext t x (fun h ↦ hx (Or.inr h))).1]
    exact hA x (fun h ↦ hx (Or.inl h)) v w hv hw
  · intro x hx
    change d.density x+t*b x=1
    rw [(hext t x (fun h ↦ hx (Or.inr h))).2]
    exact hrho x (fun h ↦ hx (Or.inl h))

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood_oai := @OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood_oai
