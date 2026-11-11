-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_packed_global_sphere_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:30.672434+00:00
-- url     : https://prove2.me/submissions/a1ef7beb-dac9-4bdc-a265-ad1191ce597d

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
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
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_independentAmbientMetric_circle_laplacian
import Theorems.Thm_OAI_Yau_Target_intrinsic_packed_positive_sphere_stage
import Theorems.Thm_OAI_Yau_Target_sphereChartTransition_divergence
import Theorems.Thm_OAI_Yau_Target_uniform_small_correction_nodal_transfer

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma product_chart_target (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    y.1 ∈ (extChartAt (𝓡 4) p.1).target ∧ y.2 ∈ (extChartAt (𝓡 1) p.2).target := by
  rw [extChartAt_prod] at hy
  exact hy

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

lemma coordDet_equiv_ne_zero (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : coordDet J.toContinuousLinearMap ≠ 0 := by
  change (LinearMap.toMatrix' J.toLinearEquiv.toLinearMap).det ≠ 0
  rw [LinearMap.det_toMatrix']
  exact J.toLinearEquiv.isUnit_det'.ne_zero

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))

include hp hrp hrad in
lemma baseChartFlux_eq_roundTensorFlux (f : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    baseChartFlux A rho f p i z = roundTensorFlux A f p i z := by
  unfold baseChartFlux roundTensorFlux sphereChartTensor
  rw [sphereChart_contravariant _ (hp _) (hrp _) p hz (hrad _)]
  simp only [Matrix.smul_apply,smul_eq_mul,baseChartMetric,baseChartDensity,
    mul_assoc,← Finset.mul_sum]
  ring

include hp hrp hrad in
lemma baseChartFlux_eq_roundTensorFlux_eventually (f : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    baseChartFlux A rho f p i =ᶠ[𝓝 z] roundTensorFlux A f p i := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with w hw
  exact baseChartFlux_eq_roundTensorFlux A rho hp hrp hrad f p hw i

include hrad in
lemma independentAmbientMetric_weighted_lift (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
    ambientWeightedChartOperator A rho f p.1 y.1 := by
  rw [independentAmbientMetric_circle_laplacian A rho hA hp hr hrp hrad f hf p hy]
  have hd (i : Fin 4) := (baseChartFlux_eq_roundTensorFlux_eventually A rho hp hrp hrad f p.1
    (product_chart_target p hy).1 i).fderiv_eq (𝕜 := ℝ)
  simp_rw [hd]
  unfold ambientWeightedChartOperator baseChartDensity
  rw [_root_.mul_inv_rev]
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_LiftedEigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma circleLift_smooth (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) :=
  hf.comp contMDiff_fst

lemma circleLift_nonzero (f : Base → ℝ) (hf : f ≠ 0) : circleLift f ≠ 0 := by
  intro h
  apply hf
  funext x
  exact congrFun h (x,1)

lemma independentAmbientMetric_eigenfunction_lift
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (hf0 : f ≠ 0)
    (lam : ℝ)
    (he : ∀ x : Base, -ambientWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam * f x) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) ∧ circleLift f ≠ 0 ∧
      ∀ x : Manifold5, -chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
        (extChartAt modelWithCorners x) (circleLift f) (extChartAt modelWithCorners x x) =
          lam * circleLift f x := by
  refine ⟨circleLift_smooth f hf,circleLift_nonzero f hf0,fun x ↦ ?_⟩
  rw [independentAmbientMetric_weighted_lift A rho hA hp hr hrp hrad f hf x
    ((extChartAt modelWithCorners x).map_source (mem_extChartAt_source x))]
  exact he x.1

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicWeightedLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)

lemma intrinsicWeightedChartOperator_eq (f : Base → ℝ) (p : Base) (z : BaseModel) :
    intrinsicWeightedChartOperator A rho f p z =
      ambientWeightedChartOperator (intrinsicAmbientMatrix A) rho f p z := by
  have he : intrinsicRoundFlux A f p = roundTensorFlux (intrinsicAmbientMatrix A) f p := by
    funext i w
    simp only [intrinsicRoundFlux,roundTensorFlux,intrinsicSphereChartTensor_eq]
  rw [intrinsicWeightedChartOperator,ambientWeightedChartOperator,he]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicLiftGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)

lemma intrinsicWeightedMetric_eigenfunction (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (hf0 : f ≠ 0) (lam : ℝ)
    (he : ∀ x : Base, -intrinsicWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam * f x) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) ∧ circleLift f ≠ 0 ∧
      ∀ x : Manifold5, -chartLaplacian (intrinsicWeightedMetric A hA hs hp rho hr hrp)
        (extChartAt modelWithCorners x) (circleLift f) (extChartAt modelWithCorners x x) =
          lam * circleLift f x := by
  apply independentAmbientMetric_eigenfunction_lift (intrinsicAmbientMatrix A) rho
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (intrinsicAmbientMatrix_radial A) f hf hf0 lam
  intro x
  simpa only [intrinsicWeightedChartOperator_eq] using he x

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SphericalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

lemma seedEigenvalue_pos {N : ℕ} (hN : 0 < N) : 0 < seedEigenvalue N := by
  unfold seedEigenvalue
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedPatchTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section

lemma seedSpherePatch_closure_subset (r : ℝ) :
    closure (seedSpherePatch r) ⊆
      (extChartAt (𝓡 4) seedPoint).symm '' closedBall (0 : BaseModel) r := by
  apply closure_minimal (image_mono ball_subset_closedBall)
  exact ((isCompact_closedBall _ _).image seedSphereChart_inverse_continuous).isClosed

lemma seedSpherePatch_closure_in_chart (r : ℝ) :
    closure (seedSpherePatch r) ⊆ (extChartAt (𝓡 4) seedPoint).source := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := seedSpherePatch_closure_subset r hx
  exact (extChartAt (𝓡 4) seedPoint).map_target (by rw [centeredSphereChart_target]; trivial)

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

omit hA hs hp hf in
lemma intrinsic_global_equation_at_center
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ∀ x : Base, -intrinsicWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam*f x := by
  intro x
  simpa only [(extChartAt (𝓡 4) x).left_inv (mem_extChartAt_source x)] using he x (extChartAt (𝓡 4) x x)

theorem intrinsic_lift_of_seed_exterior
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (hf0 : f ≠ 0) (K : Set Base) (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hseed : ∀ x, -intrinsicWeightedChartOperator A rho f seedPoint (seedCoordEquiv x) =
      lam*f (seedSphereFromCoord x))
    (hext : ∀ p z, (extChartAt (𝓡 4) p).symm z ∉ K →
      -intrinsicWeightedChartOperator A rho f p z = lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift f) ∧ circleLift f ≠ 0 ∧
      ∀ x : Manifold5, -chartLaplacian (intrinsicWeightedMetric A hA hs hp rho hr hrp)
        (extChartAt modelWithCorners x) (circleLift f) (extChartAt modelWithCorners x x) =
          lam*circleLift f x := by
  apply intrinsicWeightedMetric_eigenfunction A hA hs hp rho hr hrp f hf hf0 lam
  exact intrinsic_global_equation_at_center A rho f lam
    (intrinsic_global_equation_of_seed_exterior A hA hs hp rho f hf lam K hK hseed hext)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_HausdorffDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ENNReal NNReal

lemma ofReal_le_of_fourth_power_mul_le {A : ℝ} {C : ℝ≥0} (hC : 0 < C)
    {m : ℝ≥0∞} (h : ENNReal.ofReal A ≤ (C : ℝ≥0∞)^4*m) :
    ENNReal.ofReal (A/(C:ℝ)^4) ≤ m := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.div_le_iff' (by positivity) (by finiteness)).mpr h

end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordPatchTopology
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped Topology
noncomputable section

lemma seedCoordPatch_closure_subset (r : ℝ) :
    closure (seedCoordPatch r) ⊆ seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r :=
  closure_minimal (preimage_mono ball_subset_closedBall)
    (isClosed_closedBall.preimage seedCoordEquiv.continuous)

lemma seedCoordPatch_compactClosure (r : ℝ) : IsCompact (closure (seedCoordPatch r)) := by
  have hc : IsCompact (seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r) := by
    have he : seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r =
        seedCoordEquiv.symm '' closedBall (0 : BaseModel) r := by
      ext x
      constructor
      · intro hx
        exact ⟨seedCoordEquiv x,hx,seedCoordEquiv.symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        simpa using hy
    rw [he]
    exact (isCompact_closedBall _ _).image seedCoordEquiv.symm.continuous
  exact hc.of_isClosed_subset isClosed_closure (seedCoordPatch_closure_subset r)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_InverseSquareSmallness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
lemma eventually_inverse_square_small (C eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, C*((n:ℝ)^2)⁻¹ < eps := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ ↦ C*((n:ℝ)^2)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hpow).const_mul C
  exact ht.eventually (gt_mem_nhds heps)

end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_LiteralNodalUniformPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

theorem LiteralNodalCertificate.uniform_persistence
    {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S : _root_.OAI.Yau.Jets.Coord → ℝ}
    {Q U : Set _root_.OAI.Yau.Jets.Coord} {n : ℕ} {f : _root_.OAI.Yau.Jets.Coord → ℝ} {M : ℝ}
    (h : LiteralNodalCertificate g S Q U n f M) :
    ∃ eps > 0, ∀ v : _root_.OAI.Yau.Jets.Coord → ℝ, Continuous v →
      (∀ x, |v x-f x| < eps) →
      ENNReal.ofReal M ≤ Measure.hausdorffMeasure (4:ℝ)
        ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | v y.1 = 0}) := by
  obtain ⟨tau,rf,ht,ht4,hr,hrt,hr1,t,j,u,htQ,hdis,hU,hw,mu,hmu,hs,hp⟩ := h
  exact ⟨mu,hmu,fun v hv hclose ↦ hp v hv (fun x hx y hy ↦ hclose y)⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicPackedGlobalSphereStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicGlobalSphereStageLocalInst1 intrinsicGlobalSphereStageLocalInst2 intrinsicGlobalSphereStageLocalInst3 intrinsicGlobalSphereStageLocalInst4 intrinsicGlobalSphereStageLocalInst5 intrinsicGlobalSphereStageLocalInst6 intrinsicGlobalSphereStageLocalInst7 intrinsicGlobalSphereStageLocalInst8 intrinsicGlobalSphereStageLocalInst9 intrinsicGlobalSphereStageLocalInst10 intrinsicGlobalSphereStageLocalInst11 intrinsicGlobalSphereStageLocalInst12 intrinsicGlobalSphereStageLocalInst13 intrinsicGlobalSphereStageLocalInst14 intrinsicGlobalSphereStageLocalInst15 intrinsicGlobalSphereStageLocalInst16

theorem intrinsic_packed_global_sphere_stage_oai :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
        (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ rho : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho → (∀ x, 0 < rho x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A rho seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
      (∀ x ∉ K, ∀ v w : AmbientBase,
        ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
        A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) →
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∃ cn > 0, ∀ (T : ℝ) (J0 : ℕ),
      let k0 := max 5 (J0+2)
      let K' := 137*J0+269
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
      ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q Qw : Set Yau.Jets.Coord,
        IsCompact Qw ∧ Qw ⊆ d.Ω ∧
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
            let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
            let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
            let alpha := fun x ↦ f x*u x
            let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ u ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
            LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
              (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ∧
            ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
            tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
            (∀ x i, i ≤ J0 → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
              C*((n:ℝ)^2)⁻¹) ∧
            (∀ x, Yau.weightedDiv roundCoordDensity
              (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x) ∧
            ∃ ug ag bg : Base → ℝ,
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ug ∧
              tsupport (ug-sphericalSeed n) ⊆ seedSphereFromCoord '' Qw ∧
              (∀ x, ug (seedSphereFromCoord x) = u x) ∧
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ag ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ bg ∧
              tsupport ag ⊆ seedSphereFromCoord '' Q ∧ tsupport bg ⊆ seedSphereFromCoord '' Q ∧
              (∀ x, ag (seedSphereFromCoord x) = alpha x) ∧
              (∀ x, bg (seedSphereFromCoord x) = beta x) ∧
              (∀ x, |ag x| ≤ C*((n:ℝ)^2)⁻¹) ∧ (∀ x, |bg x| ≤ C*((n:ℝ)^2)⁻¹) ∧
              ∃ hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation ag x),
              ∃ hnewSym : (∀ x v w, (A x+roundTensorPerturbation ag x) v w =
                (A x+roundTensorPerturbation ag x) w v),
              ∃ hnewPos : (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation ag x) v v),
              ∃ hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+bg x),
              ∃ hrnewPos : (∀ x, 0 < rho x+bg x), ug ≠ 0 ∧
              (∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
                (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x)) ∧
              (∀ x i j k, i ≤ J0 →
                ‖iteratedFDeriv ℝ i (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation ag)
                  seedPoint (seedCoordEquiv y) j k) x‖ ≤ C*((n:ℝ)^2)⁻¹) ∧
              (∀ p z, -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation ag x)
                (fun x ↦ rho x+bg x) ug p z = seedEigenvalue n*ug ((extChartAt (𝓡 4) p).symm z)) ∧
              ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift ug) ∧ circleLift ug ≠ 0 ∧
              (∀ x : Manifold5, -chartLaplacian
                (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                  (fun x ↦ rho x+bg x) hrnew hrnewPos)
                (extChartAt modelWithCorners x) (circleLift ug) (extChartAt modelWithCorners x x) =
                  seedEigenvalue n*circleLift ug x) ∧
              0 < seedEigenvalue n ∧
              ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
                sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
                nodalMeasure
                  (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                    (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift ug) ∧
              ∃ eps > 0, ∀ vg : Base → ℝ,
                Continuous (fun x ↦ vg (seedSphereFromCoord x)) →
                (∀ x, |vg x-ug x| < eps) →
                ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
                  sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
                  nodalMeasure
                    (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                      (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift vg) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_positive_sphere_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨c,hc,hstage⟩ := hstage A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨eta,heta,Cproj,hCproj,htransfer⟩ := uniform_small_correction_nodal_transfer
    A hAs hs hp rho hrs hrp (seedCoordPatch_compactClosure r)
  refine ⟨c,hc,c/(Cproj:ℝ)^4,by positivity,?_⟩
  intro T J0 k0 K'
  obtain ⟨d,b,hb,C,hC,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,hselect⟩ :=
    hstage T J0
  refine ⟨d,b,hb,C,hC,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hselect,eventually_inverse_square_small C eta heta,eventually_gt_atTop (0:ℕ)] with n hn hnSmall hn0
  obtain ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,hsize,heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed,htensor,hext⟩ := hn
  let := hfin
  have hsource : K ∪ seedSphereFromCoord '' (Q ∪ Qw) ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro x (hx | ⟨y,hy,rfl⟩)
    · exact seedSpherePatch_closure_in_chart r (subset_closure (hKP hx))
    · exact seedSphereFromCoord_source y
  have hall := intrinsic_global_equation_of_seed_exterior _ hnew hnewSym hnewPos _ ug hug
    (seedEigenvalue n) _ hsource hfixed hext
  have hlift := intrinsic_lift_of_seed_exterior _ hnew hnewSym hnewPos _ ug hug
    (seedEigenvalue n) hrnew hrnewPos hugne _ hsource hfixed hext
  have hm := htransfer ag bg hnew hnewSym hnewPos hrnew hrnewPos
    (fun x ↦ (hagB x).trans hnSmall.le) (fun x ↦ (hbgB x).trans hnSmall.le)
    _ ug d.U
    (fun x hx ↦ subset_closure (d.closure_Ω_patch (subset_closure (d.closure_U_Ω (subset_closure hx)))))
    hugval
  have hnodal := ofReal_le_of_fourth_power_mul_le hCproj (hmeasure.trans hm)
  refine ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,hsize,heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed,htensor,hall,
    hlift.1,hlift.2.1,hlift.2.2,seedEigenvalue_pos hn0,?_,?_⟩
  · simpa only [div_mul_eq_mul_div] using hnodal
  · obtain ⟨eps,heps,hpersist⟩ := hpacking.uniform_persistence
    refine ⟨eps,heps,?_⟩
    intro vg hv hclose
    have hcoord := hpersist (fun x ↦ vg (seedSphereFromCoord x)) hv (fun x ↦ by
      simpa only [hugval] using hclose (seedSphereFromCoord x))
    have hm' := htransfer ag bg hnew hnewSym hnewPos hrnew hrnewPos
      (fun x ↦ (hagB x).trans hnSmall.le) (fun x ↦ (hbgB x).trans hnSmall.le)
      (fun x ↦ vg (seedSphereFromCoord x)) vg d.U
      (fun x hx ↦ subset_closure (d.closure_Ω_patch (subset_closure (d.closure_U_Ω (subset_closure hx)))))
      (fun x ↦ rfl)
    have hnodal' := ofReal_le_of_fourth_power_mul_le hCproj (hcoord.trans hm')
    simpa only [div_mul_eq_mul_div] using hnodal'

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_packed_global_sphere_stage_oai := @OAI.Yau.Target.intrinsic_packed_global_sphere_stage_oai
