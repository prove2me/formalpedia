-- Prove2me | solution 1 for OAI.Yau.Target.sphere_resolvent_finite_variational_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:33.326689+00:00
-- url     : https://prove2.me/submissions/dc34b354-073d-457d-b690-d120fa9fb43e

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
import Theorems.Thm_OAI_Yau_Target_sphereL2Resolvent_compact

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

namespace SphereEnergySmooth
variable (d : SphereEnergyData)

theorem norm_sq (u : SphereEnergySmooth d) :
    ‖u‖^2 = sphereWeightedPairing d.density (toSmooth d u) (toSmooth d u) +
      sphereDirichletForm d.tensor (toSmooth d u) (toSmooth d u) := by
  exact (real_inner_self_eq_norm_sq u).symm

end SphereEnergySmooth

theorem sphereEnergyToCompletion_dense (d : SphereEnergyData) :
    DenseRange (sphereEnergyToCompletion d) := UniformSpace.Completion.denseRange_coe

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
open scoped ENNReal
noncomputable section

attribute [local instance] OAI.Yau.Target.sphereWeightedL2Measurable
attribute [local instance] OAI.Yau.Target.sphereWeightedL2Borel
theorem sphereWeightedToLp_inner (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u v : Base → ℝ) (hu : Continuous u) (hv : Continuous v) :
    inner ℝ (sphereWeightedToLp rho hr hp u hu) (sphereWeightedToLp rho hr hp v hv) =
      sphereWeightedPairing rho u v := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, u x*v x ∂sphereWeightedMeasure rho := by
      apply integral_congr_ae
      filter_upwards [(sphereWeighted_memLp rho hr hp u hu).coeFn_toLp,
        (sphereWeighted_memLp rho hr hp v hv).coeFn_toLp] with x hx hy
      simp only [sphereWeightedToLp] at *
      rw [hx,hy]
      change v x*u x = u x*v x
      ring
    _ = _ := by
      rw [sphereWeightedMeasure_integral rho hr hp]
      simp only [sphereWeightedPairing,mul_assoc]

theorem sphereWeightedToLp_norm_sq (rho : Base → ℝ) (hr : Continuous rho)
    (hp : ∀ x, 0 ≤ rho x) (u : Base → ℝ) (hu : Continuous u) :
    ‖sphereWeightedToLp rho hr hp u hu‖^2 = sphereWeightedPairing rho u u := by
  rw [← real_inner_self_eq_norm_sq,sphereWeightedToLp_inner]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyL2Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereEnergyL2MapMeasurable_r30e34f_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_r30e34f_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereEnergyL2Linear_norm_sq (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    ‖sphereEnergyL2Linear d u‖^2 =
      sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u) :=
  sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le)
    (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous

theorem sphereEnergyL2Linear_norm_le (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    ‖sphereEnergyL2Linear d u‖ ≤ ‖u‖ := by
  have h := SphereEnergySmooth.norm_sq d u
  have he := sphereDirichletForm_nonneg d.tensor d.pos (SphereEnergySmooth.toSmooth d u)
  have hl := sphereEnergyL2Linear_norm_sq d u
  nlinarith [norm_nonneg u,norm_nonneg (sphereEnergyL2Linear d u)]

theorem sphereEnergyL2Map_coe (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    sphereEnergyL2Map d (sphereEnergyToCompletion d u) = sphereEnergyL2Linear d u := by
  apply LinearMap.extendOfNorm_eq (sphereEnergyToCompletion_dense d)
  refine ⟨1,fun v ↦ ?_⟩
  simpa using sphereEnergyL2Linear_norm_le d v

theorem sphereEnergyL2Map_norm_le (d : SphereEnergyData) : ‖sphereEnergyL2Map d‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (sphereEnergyToCompletion_dense d) zero_le_one
  intro u
  simpa using sphereEnergyL2Linear_norm_le d u

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothL2Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] OAI.Yau.Target.sphereSmoothL2DensityMeasurable
local instance sphereSmoothL2DensityBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereSmoothToContinuous_dense (d : SphereEnergyData) : DenseRange (sphereSmoothToContinuous d) := by
  rw [Metric.denseRange_iff]
  intro f eps heps
  obtain ⟨g,hg,-⟩ := f.continuous.exists_contMDiff_approx (𝓡 4) (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : Base ↦ eps/2)) (fun _ ↦ half_pos heps)
  let u : SphereEnergySmooth d := (⟨g,g.contMDiff⟩ : sphereSmoothFunctions)
  refine ⟨u,lt_of_le_of_lt ?_ (half_lt_self heps)⟩
  apply (ContinuousMap.dist_le (half_pos heps).le).mpr
  intro x
  change dist (f x) (g x) ≤ eps/2
  rw [dist_comm]
  exact (hg x).le

theorem sphereEnergyL2Linear_dense (d : SphereEnergyData) : DenseRange (sphereEnergyL2Linear d) := by
  let := sphereWeightedMeasure_finite d.density d.continuous (fun x ↦ (d.positive x).le)
  have hd := (ContinuousMap.toLp_denseRange (E := ℝ) (μ := sphereWeightedMeasure d.density) (𝕜 := ℝ) (p := 2) (by simp)).comp
    (sphereSmoothToContinuous_dense d) (ContinuousMap.toLp 2 (sphereWeightedMeasure d.density) ℝ).continuous
  have heq : (ContinuousMap.toLp 2 (sphereWeightedMeasure d.density) ℝ) ∘ sphereSmoothToContinuous d =
      sphereEnergyL2Linear d := by
    funext u
    apply Lp.ext
    exact ((sphereSmoothToContinuous d u).coeFn_toLp (sphereWeightedMeasure d.density)).trans
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
        (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u).property.continuous).coeFn_toLp.symm
  rwa [heq] at hd

theorem sphereEnergyL2Map_dense (d : SphereEnergyData) : DenseRange (sphereEnergyL2Map d) := by
  apply (sphereEnergyL2Linear_dense d).mono
  rintro _ ⟨u,rfl⟩
  exact ⟨sphereEnergyToCompletion d u,sphereEnergyL2Map_coe d u⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereWeakResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Filter
open scoped InnerProduct
noncomputable section

local instance sphereWeakResolventMeasurable_r30e34f_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_r30e34f_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereWeakSolution_spec (d : SphereEnergyData) (f : SphereWeightedL2 d) (v : SphereEnergyHilbert d) :
    inner ℝ (sphereWeakSolution d f) v = inner ℝ f (sphereEnergyL2Map d v) :=
  (sphereEnergyL2Map d).adjoint_inner_left v f

theorem sphereWeakSolution_eq_zero_iff (d : SphereEnergyData) (f : SphereWeightedL2 d) :
    sphereWeakSolution d f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hclosed : IsClosed {v : SphereWeightedL2 d | inner ℝ f v = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    exact (sphereEnergyL2Map_dense d).induction_on (p := fun v ↦ inner ℝ f v = 0) f hclosed (fun u ↦ by
      rw [← sphereWeakSolution_spec,hf,inner_zero_left])
  · rintro rfl
    exact map_zero _

theorem sphereL2Resolvent_inner (d : SphereEnergyData) (f g : SphereWeightedL2 d) :
    inner ℝ (sphereL2Resolvent d f) g = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := by
  exact ((sphereEnergyL2Map d).adjoint_inner_right (sphereWeakSolution d f) g).symm

theorem sphereL2Resolvent_symmetric (d : SphereEnergyData) : (sphereL2Resolvent d).IsSymmetric := by
  intro f g
  change inner ℝ (sphereL2Resolvent d f) g = inner ℝ f (sphereL2Resolvent d g)
  calc
    _ = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := sphereL2Resolvent_inner d f g
    _ = inner ℝ (sphereWeakSolution d g) (sphereWeakSolution d f) := real_inner_comm _ _
    _ = inner ℝ (sphereL2Resolvent d g) f := (sphereL2Resolvent_inner d g f).symm
    _ = _ := real_inner_comm _ _

theorem sphereL2Resolvent_positive (d : SphereEnergyData) (f : SphereWeightedL2 d) (hf : f ≠ 0) :
    0 < inner ℝ (sphereL2Resolvent d f) f := by
  rw [sphereL2Resolvent_inner,real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h ↦ hf ((sphereWeakSolution_eq_zero_iff d f).mp h)))

theorem sphereL2Resolvent_norm_le (d : SphereEnergyData) : ‖sphereL2Resolvent d‖ ≤ 1 := by
  have ha : ‖sphereWeakSolution d‖ = ‖sphereEnergyL2Map d‖ :=
    ContinuousLinearMap.adjoint.norm_map (sphereEnergyL2Map d)
  have h := ContinuousLinearMap.opNorm_comp_le (sphereEnergyL2Map d) (sphereWeakSolution d)
  rw [ha] at h
  apply h.trans
  nlinarith [sphereEnergyL2Map_norm_le d,norm_nonneg (sphereEnergyL2Map d)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereResolventSpectrumMeasurable_r30e34f_1 : MeasurableSpace Base := borel Base
local instance sphereResolventSpectrumBorel_r30e34f_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereL2Resolvent_eigenvalue_bounds (d : SphereEnergyData) (mu : ℝ) (f : SphereWeightedL2 d)
    (hf : f ≠ 0) (he : sphereL2Resolvent d f = mu • f) : 0 < mu ∧ mu ≤ 1 := by
  have hpos := sphereL2Resolvent_positive d f hf
  rw [he,inner_smul_left_eq_smul,real_inner_self_eq_norm_sq,smul_eq_mul] at hpos
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hm : 0 < mu := (mul_pos_iff_of_pos_right (sq_pos_of_pos hn)).mp hpos
  refine ⟨hm,?_⟩
  have h := (sphereL2Resolvent d).le_opNorm f
  have hb := mul_le_mul_of_nonneg_right (sphereL2Resolvent_norm_le d) (norm_nonneg f)
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hm] at h
  nlinarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereSmoothResolventBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section

local instance sphereSmoothResolventBridgeMeasurable_r30e34f_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothResolventBridgeBorel_r30e34f_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereEnergyL2Linear_eq_zero_iff (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    sphereEnergyL2Linear d u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    by_contra hn
    have hfun : (SphereEnergySmooth.toSmooth d u : Base → ℝ) ≠ 0 := by
      intro hf
      apply hn
      exact Subtype.ext hf
    have hp := sphereWeightedPairing_self_pos d.density (SphereEnergySmooth.toSmooth d u)
      d.continuous d.positive (SphereEnergySmooth.toSmooth d u).property.continuous hfun
    have he := sphereEnergyL2Linear_norm_sq d u
    rw [hu,norm_zero,zero_pow (by decide : 2 ≠ 0)] at he
    exact (ne_of_gt hp) he.symm
  · rintro rfl
    exact map_zero _

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL2Infinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

local instance sphereL2InfiniteMeasurable_r30e34f_1 : MeasurableSpace Base := borel Base
local instance sphereL2InfiniteBorel_r30e34f_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_distinct_points (N : ℕ) :
    ∃ p : Fin N → Base, Function.Injective p := by
  refine ⟨fun i ↦ seedSphereFromCoord (fun _ ↦ (i.val : ℝ)),?_⟩
  intro i j hij
  have h := congrArg seedSphereToCoord hij
  simp only [seedSphereToCoord_from] at h
  have hv := congrFun h (0 : Fin 4)
  apply Fin.ext
  exact_mod_cast hv

theorem sphere_smooth_finite_interpolation (d : SphereEnergyData) {N : ℕ}
    (p : Fin N → Base) (hp : Function.Injective p) :
    ∃ f : Fin N → SphereEnergySmooth d,
      ∀ i j, (SphereEnergySmooth.toSmooth d (f i) : Base → ℝ) (p j) =
        if i = j then 1 else 0 := by
  classical
  have hex (i : Fin N) : ∃ u : SphereEnergySmooth d,
      ∀ j, (SphereEnergySmooth.toSmooth d u : Base → ℝ) (p j) =
        if i = j then 1 else 0 := by
    let s : Set Base := p '' {j | j ≠ i}
    have hs : IsClosed s := ((Set.toFinite {j : Fin N | j ≠ i}).image p).isClosed
    have hd : Disjoint s {p i} := by
      apply disjoint_singleton_right.mpr
      rintro ⟨j,hj,hji⟩
      exact hj (hp hji)
    obtain ⟨g,hg0,hg1,-⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := ⊤)
      (𝓡 4) hs isClosed_singleton hd
    refine ⟨(⟨g,g.contMDiff⟩ : sphereSmoothFunctions),?_⟩
    intro j
    change g (p j) = _
    by_cases hij : i = j
    · subst j
      simpa using hg1 (mem_singleton (p i))
    · have hj : p j ∈ s := ⟨j,Ne.symm hij,rfl⟩
      simpa [hij] using hg0 hj
  choose f hf using hex
  exact ⟨f,hf⟩

theorem sphere_smooth_arbitrary_independent (d : SphereEnergyData) (N : ℕ) :
    ∃ f : Fin N → SphereEnergySmooth d, LinearIndependent ℝ f := by
  classical
  obtain ⟨p,hp⟩ := sphere_finite_distinct_points N
  obtain ⟨f,hf⟩ := sphere_smooth_finite_interpolation d p hp
  refine ⟨f,Fintype.linearIndependent_iff.mpr ?_⟩
  intro c hc j
  let ev : SphereEnergySmooth d →ₗ[ℝ] ℝ :=
    (LinearMap.proj (p j)).comp sphereSmoothFunctions.subtype
  have h := congrArg ev hc
  simp only [map_sum,map_smul,map_zero] at h
  change (∑ i, c i * (SphereEnergySmooth.toSmooth d (f i) : Base → ℝ) (p j)) = 0 at h
  simpa [hf] using h

theorem sphereWeightedL2_infiniteDimensional (d : SphereEnergyData) :
    ¬FiniteDimensional ℝ (SphereWeightedL2 d) := by
  intro hdim
  let := hdim
  have hinj : Function.Injective (sphereEnergyL2Linear d) := by
    apply (sphereEnergyL2Linear d).ker_eq_bot.mp
    exact LinearMap.ker_eq_bot'.mpr (fun u hu ↦ (sphereEnergyL2Linear_eq_zero_iff d u).mp hu)
  obtain ⟨f,hf⟩ := sphere_smooth_arbitrary_independent d
    (Module.finrank ℝ (SphereWeightedL2 d)+1)
  have hli := hf.map' (sphereEnergyL2Linear d) ((sphereEnergyL2Linear d).ker_eq_bot.mpr hinj)
  have hc := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  omega

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_CompactPositiveMaxEigenvector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Filter Set Module.End
noncomputable section

theorem compact_positive_max_eigenvector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ (T x) x) (hT : T ≠ 0) :
    ∃ v : E, ‖v‖=1 ∧ T v=‖T‖ • v ∧
      inner ℝ (T v) v=‖T‖ ∧ ∀ x : E, inner ℝ (T x) x ≤ ‖T‖*‖x‖^2 := by
  have hn : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hspec : ‖T‖ ∈ spectrum ℝ T ∨ -‖T‖ ∈ spectrum ℝ T := by
    by_contra! h
    have h1 : ‖T‖ ∈ resolventSet ℝ T := by simpa only [spectrum,mem_compl_iff,not_not] using h.1
    have h2 : -‖T‖ ∈ resolventSet ℝ T := by simpa only [spectrum,mem_compl_iff,not_not] using h.2
    obtain ⟨c,hc0,hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h1 h2
    have hb : (⨆ x, |T.rayleighQuotient x|) ≤ ‖T‖-c := ciSup_le hc
    rw [← T.norm_eq_iSup_rayleighQuotient hs] at hb
    linarith
  have he : HasEigenvalue T.toLinearMap ‖T‖ := by
    rcases hspec with h | h
    · exact (hc.hasEigenvalue_iff_mem_spectrum hn.ne').mpr h
    · obtain ⟨v,hv⟩ := ((hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hn.ne')).mpr h).exists_hasEigenvector
      have heq : T v = -‖T‖ • v := hv.apply_eq_smul
      have hh := hp v
      rw [heq,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq] at hh
      have hvpos : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv.2)
      nlinarith
  obtain ⟨v,hv⟩ := he.exists_hasEigenvector
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  let u := ‖v‖⁻¹ • v
  have hun : ‖u‖=1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hvnorm]
  have heq : T v=‖T‖ • v := hv.apply_eq_smul
  have hue : T u=‖T‖ • u := by
    dsimp [u]
    rw [map_smul,heq,smul_comm]
  refine ⟨u,hun,hue,?_,?_⟩
  · rw [hue,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq,hun]
    ring
  · intro x
    calc
      inner ℝ (T x) x ≤ ‖T x‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)
      _ = ‖T‖*‖x‖^2 := by ring

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_CompactPositiveInvariantMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem compact_positive_invariant_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    (hInv : ∀ x ∈ V, T x ∈ V) (x : E) (hxV : x ∈ V) (hx : x ≠ 0) :
    ∃ mu > 0, ∃ v : E, v ∈ V ∧ ‖v‖=1 ∧ T v=mu • v ∧
      ∀ y ∈ V, inner ℝ (T y) y ≤ mu*‖y‖^2 := by
  let : CompleteSpace V := hV.completeSpace_coe
  let : Nontrivial V := ⟨⟨⟨x,hxV⟩,0,fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  let S : V →L[ℝ] V := T.restrict hInv
  have hS : S ≠ 0 := by
    intro hz
    have hh : 0 < inner ℝ (S ⟨x,hxV⟩) (⟨x,hxV⟩ : V) := hp x hx
    rw [hz,zero_apply,inner_zero_left] at hh
    exact (lt_irrefl 0) hh
  have hSp : ∀ v : V, 0 ≤ inner ℝ (S v) v := by
    intro v
    by_cases hz : (v : E)=0
    · have hv : v=0 := Subtype.ext hz
      simp only [hv,map_zero,inner_zero_left,le_refl]
    · exact (hp v hz).le
  obtain ⟨v,hvn,hve,hvi,hmax⟩ := compact_positive_max_eigenvector S
    (hc.restrict' hInv) (hs.restrict_invariant hInv) hSp hS
  have hnorm : (0 : ℝ) < ‖S‖ := lt_of_le_of_ne (norm_nonneg S)
    (fun hz ↦ hS ((ContinuousLinearMap.opNorm_zero_iff S).mp hz.symm))
  refine ⟨‖S‖,hnorm,(v : E),v.property,hvn,?_,?_⟩
  · exact congrArg Subtype.val hve
  · intro y hy
    exact hmax ⟨y,hy⟩

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_CompactEigenfamilyComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem eigenfamily_orthogonal_invariant {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hs : T.IsSymmetric)
    (e : I → E) (mu : I → ℝ) (he : ∀ i, T (e i)=mu i • e i) :
    ∀ x ∈ (Submodule.span ℝ (range e))ᗮ, T x ∈ (Submodule.span ℝ (range e))ᗮ := by
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,rfl⟩ := hy
    have hh := hx (e i) (Submodule.subset_span (mem_range_self i))
    have hsym : inner ℝ (T (e i)) x = inner ℝ (e i) (T x) := hs (e i) x
    rw [← hsym,he i,inner_smul_left_eq_smul,smul_eq_mul,hh,mul_zero]
  | zero => exact inner_zero_left _
  | add y z hy hz ihy ihz => rw [inner_add_left,ihy,ihz,add_zero]
  | smul a y hy ih => rw [inner_smul_left_eq_smul,smul_eq_mul,ih,mul_zero]

theorem compact_positive_eigenfamily_extension {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (e : I → E) (mu : I → ℝ) (he : ∀ i, T (e i)=mu i • e i)
    (x : E) (hx : x ∈ (Submodule.span ℝ (range e))ᗮ) (hx0 : x ≠ 0) :
    ∃ lam > 0, ∃ v : E, ‖v‖=1 ∧ T v=lam • v ∧
      (∀ i, inner ℝ (e i) v=0) ∧
      (∀ y ∈ (Submodule.span ℝ (range e))ᗮ, inner ℝ (T y) y ≤ lam*‖y‖^2) := by
  obtain ⟨lam,hlam,v,hv,hvn,hve,hmax⟩ := compact_positive_invariant_max T hc hs hp
    (Submodule.span ℝ (range e))ᗮ (Submodule.isClosed_orthogonal _)
    (eigenfamily_orthogonal_invariant T hs e mu he) x hx hx0
  exact ⟨lam,hlam,v,hvn,hve,fun i ↦ hv (e i) (Submodule.subset_span (mem_range_self i)),hmax⟩

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteFamilyNonzeroComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem finite_family_nonzero_complement {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Finite I]
    (hE : ¬FiniteDimensional ℝ E) (e : I → E) :
    ∃ x : E, x ∈ (Submodule.span ℝ (range e))ᗮ ∧ x ≠ 0 := by
  let V := Submodule.span ℝ (range e)
  let : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (finite_range e)
  have hV : V ≠ ⊤ := by
    intro h
    apply hE
    apply FiniteDimensional.of_surjective V.subtype
    intro x
    exact ⟨⟨x,by rw [h]; trivial⟩,rfl⟩
  have horth : Vᗮ ≠ ⊥ := fun h ↦ hV (Submodule.orthogonal_eq_bot_iff.mp h)
  exact Submodule.exists_mem_ne_zero_of_ne_bot horth

theorem compact_positive_finite_family_extension {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Finite I]
    (hE : ¬FiniteDimensional ℝ E)
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (e : I → E) (mu : I → ℝ) (he : ∀ i, T (e i)=mu i • e i) :
    ∃ lam > 0, ∃ v : E, ‖v‖=1 ∧ T v=lam • v ∧
      (∀ i, inner ℝ (e i) v=0) ∧
      (∀ y ∈ (Submodule.span ℝ (range e))ᗮ, inner ℝ (T y) y ≤ lam*‖y‖^2) := by
  obtain ⟨x,hx,hx0⟩ := finite_family_nonzero_complement hE e
  exact compact_positive_eigenfamily_extension T hc hs hp e mu he x hx hx0

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_FiniteVariationalEigenframe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem real_orthogonal_span_range {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e : I → E) (x : E)
    (h : ∀ i, inner ℝ (e i) x = 0) :
    x ∈ (Submodule.span ℝ (range e))ᗮ := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨i,rfl⟩ := hy; exact h i
  | zero => exact inner_zero_left _
  | add y z hy hz ihy ihz => rw [inner_add_left,ihy,ihz,add_zero]
  | smul a y hy ih => rw [inner_smul_left_eq_smul,smul_eq_mul,ih,mul_zero]

theorem real_orthonormal_snoc {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : ℕ} (e : Fin N → E) (v : E)
    (he : Orthonormal ℝ e) (hv : ‖v‖ = 1)
    (ho : ∀ i, inner ℝ (e i) v = 0) : Orthonormal ℝ (Fin.snoc e v) := by
  rw [orthonormal_iff_ite]
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp [hv]
  · rename_i j
    rw [Fin.snoc_last,Fin.snoc_castSucc,real_inner_comm,ho j]
    simp [ne_of_gt (Fin.castSucc_lt_last j)]
  · simp [ho]
  · simpa using (orthonormal_iff_ite.mp he _ _)

theorem compact_positive_finite_variational_eigenframe {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hE : ¬FiniteDimensional ℝ E)
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x) (N : ℕ) :
    ∃ (e : Fin N → E) (mu : Fin N → ℝ),
      Orthonormal ℝ e ∧ (∀ i, 0 < mu i ∧ T (e i) = mu i • e i) ∧
      Antitone mu ∧ ∀ i x,
        (∀ j, j < i → inner ℝ (e j) x = 0) →
        inner ℝ (T x) x ≤ mu i * ‖x‖^2 := by
  classical
  induction N with
  | zero =>
    refine ⟨Fin.elim0,Fin.elim0,?_,?_,?_,?_⟩
    · exact ⟨fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i⟩
    · exact fun i ↦ Fin.elim0 i
    · exact fun i ↦ Fin.elim0 i
    · exact fun i ↦ Fin.elim0 i
  | succ N ih =>
    obtain ⟨e,mu,he,heig,hanti,hmax⟩ := ih
    obtain ⟨lam,hlam,v,hvn,hve,horth,hvmax⟩ :=
      compact_positive_finite_family_extension hE T hc hs hp e mu (fun i ↦ (heig i).2)
    have hlam_le (i : Fin N) : lam ≤ mu i := by
      have h := hmax i v (fun j _ ↦ horth j)
      rw [hve,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq,hvn] at h
      simpa using h
    refine ⟨Fin.snoc e v,Fin.snoc mu lam,real_orthonormal_snoc e v he hvn horth,?_,?_,?_⟩
    · intro i
      induction i using Fin.lastCases
      · simpa using And.intro hlam hve
      · simpa using heig _
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact le_rfl
      · simp at hij
      · simpa using hlam_le _
      · simpa using hanti (by simpa using hij)
    · intro i x hx
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        apply hvmax x
        apply real_orthogonal_span_range e x
        intro j
        simpa using hx j.castSucc (Fin.castSucc_lt_last j)
      | cast i =>
        rw [Fin.snoc_castSucc]
        apply hmax i x
        intro j hji
        simpa using hx j.castSucc (by simpa using hji)

end
end Yau.Analysis

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

local instance sphereFiniteFrameMeasurable_r30e34f_1 : MeasurableSpace Base := borel Base
local instance sphereFiniteFrameBorel_r30e34f_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_finite_variational_frame_oai (d : SphereEnergyData) (N : ℕ) :
    ∃ (e : Fin N → SphereWeightedL2 d) (mu : Fin N → ℝ),
      Orthonormal ℝ e ∧
      (∀ i, 0 < mu i ∧ mu i ≤ 1 ∧ sphereL2Resolvent d (e i) = mu i • e i) ∧
      Antitone mu ∧ ∀ i x,
        (∀ j, j < i → inner ℝ (e j) x = 0) →
        inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2 := by
  obtain ⟨e,mu,he,heig,hanti,hmax⟩ := compact_positive_finite_variational_eigenframe
    (sphereWeightedL2_infiniteDimensional d) (sphereL2Resolvent d)
    (sphereL2Resolvent_compact d) (sphereL2Resolvent_symmetric d)
    (sphereL2Resolvent_positive d) N
  exact ⟨e,mu,he,fun i ↦ ⟨(heig i).1,
    (sphereL2Resolvent_eigenvalue_bounds d (mu i) (e i) (he.ne_zero i) (heig i).2).2,
    (heig i).2⟩,hanti,hmax⟩

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_resolvent_finite_variational_frame_oai := @OAI.Yau.Target.sphere_resolvent_finite_variational_frame_oai
