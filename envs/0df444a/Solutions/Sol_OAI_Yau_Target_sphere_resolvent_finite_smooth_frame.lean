-- Prove2me | solution 1 for OAI.Yau.Target.sphere_resolvent_finite_smooth_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:31.998813+00:00
-- url     : https://prove2.me/submissions/34ba3bff-dad4-4837-ae7d-bcf336d93ffa

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
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
import Mathlib.Geometry.Manifold.SmoothApprox
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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_global_representative
import Theorems.Thm_OAI_Yau_Target_sphere_resolvent_finite_variational_frame

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereEigenGlobalNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] sphereGlobalRepresentativeMeasurable sphereGlobalRepresentativeBorel

theorem sphere_L2_representative_pairing (d : SphereEnergyData) (f : SphereWeightedL2 d)
    (u : Base → ℝ) (ha : u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ)) :
    sphereWeightedPairing d.density u u=‖f‖^2 := by
  rw [sphereWeightedPairing,sphereWeightedL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(sphereWeightedMeasure_ae_iff d _).mp ha] with x hx
  rw [hx]
  ring

theorem sphere_eigen_global_normalized (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (heigen : sphereL2Resolvent d f=mu • f) (hn : ‖f‖=1) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      u =ᵐ[sphereWeightedMeasure d.density] (f : Base → ℝ) ∧
      sphereWeightedPairing d.density u u=1 ∧ u ≠ 0 ∧
      ∀ p x, x ∈ interior (Yau.realCenteredCube 4 (1/64)) →
        Yau.coordDiv (realMatrixFlux (sphereChartPrincipalDensity d p) (u ∘ sphereChartCoordMap p)) x+
          sphereEigenForcingCoefficient d p mu x*u (sphereChartCoordMap p x)=0 := by
  obtain ⟨u,hu,ha,he⟩ := sphere_eigen_global_representative d hrho mu hmu f heigen
  have hnorm : sphereWeightedPairing d.density u u=1 := by
    rw [sphere_L2_representative_pairing d f u ha,hn,one_pow]
  refine ⟨u,hu,ha,hnorm,?_,he⟩
  intro hz
  simp only [hz,sphereWeightedPairing,Pi.zero_apply,mul_zero,integral_zero] at hnorm
  norm_num at hnorm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteVariationalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Analysis
open scoped ContDiff
noncomputable section

local instance sphereFiniteFrameMeasurable_re561a4_1 : MeasurableSpace Base := borel Base
local instance sphereFiniteFrameBorel_re561a4_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_finite_smooth_frame_oai (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ (u : Fin N → SphereEnergySmooth d) (mu : Fin N → ℝ),
      Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)) ∧
      (∀ i, 0 < mu i ∧ mu i ≤ 1 ∧
        sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i)) ∧
      Antitone mu ∧ ∀ i x,
        (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
        inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2 := by
  classical
  obtain ⟨e,mu,he,heig,hanti,hmax⟩ := sphere_resolvent_finite_variational_frame d N
  have hex (i : Fin N) : ∃ u : SphereEnergySmooth d, sphereEnergyL2Linear d u = e i := by
    obtain ⟨v,hv,ha,-⟩ := sphere_eigen_global_normalized d hrho (mu i) (heig i).1.ne'
      (e i) (heig i).2.2 (he.norm_eq_one i)
    refine ⟨(⟨v,hv⟩ : sphereSmoothFunctions),?_⟩
    apply Lp.ext
    exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
      v hv.continuous).coeFn_toLp.trans ha
  choose u hu using hex
  refine ⟨u,mu,?_,?_,hanti,?_⟩
  · simpa only [hu] using he
  · simpa only [hu] using heig
  · simpa only [hu] using hmax

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_resolvent_finite_smooth_frame_oai := @OAI.Yau.Target.sphere_resolvent_finite_smooth_frame_oai
