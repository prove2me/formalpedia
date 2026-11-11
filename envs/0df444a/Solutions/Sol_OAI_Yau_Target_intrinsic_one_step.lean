-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_one_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:36:03.45121+00:00
-- url     : https://prove2.me/submissions/4871418b-ef0d-4f0a-bc93-60941f71618e

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
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
import Mathlib.MeasureTheory.Covering.Vitali
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
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
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_intrinsic_packed_global_sphere_stage
import Theorems.Thm_OAI_Yau_Target_sphere_reference_literal_nodal_persistence
import Theorems.Thm_OAI_Yau_Target_sphere_simplicity_in_comparison_neighborhood

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

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

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

lemma metricGradient_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (metricGradient g S) :=
  (positive_metric_inverse_continuous g hg.continuous hp).clm_apply
    (hS.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end
end Yau.Geometry

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

lemma finiteChartDerivativeSize_add_le (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    (J : ℕ) (f g : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p))
    (hg : ∀ p ∈ P, ContDiff ℝ ∞ (g p)) :
    finiteChartDerivativeSize P Q J (fun p x ↦ f p x+g p x) ≤
      finiteChartDerivativeSize P Q J f+finiteChartDerivativeSize P Q J g := by
  apply finiteChartDerivativeSize_le _ _ _ _
    (add_nonneg (finiteChartDerivativeSize_nonneg P hQ J f hf) (finiteChartDerivativeSize_nonneg P hQ J g hg))
  intro p hp i hi x hx
  rw [fun_iteratedFDeriv_add_apply
    ((hf p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((hg p hp).of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_le_finiteChartDerivativeSize P hQ J f hf p hp i hi x hx)
    (norm_le_finiteChartDerivativeSize P hQ J g hg p hp i hi x hx))

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

lemma finiteChartDerivativeSize_mono_order (P : Finset I) {Q : Set E} (hQ : IsCompact Q)
    {J K : ℕ} (hJK : J ≤ K) (f : I → E → F) (hf : ∀ p ∈ P, ContDiff ℝ ∞ (f p)) :
    finiteChartDerivativeSize P Q J f ≤ finiteChartDerivativeSize P Q K f := by
  apply finiteChartDerivativeSize_le _ _ _ _ (finiteChartDerivativeSize_nonneg P hQ K f hf)
  intro p hp i hi x hx
  exact norm_le_finiteChartDerivativeSize P hQ K f hf p hp i (hi.trans hJK) x hx

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

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

lemma metric_inverse_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (x : T) (hg : ContinuousAt g x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ ContinuousLinearMap.inverse (g y)) x := by
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g x) hp)).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g x) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact hc'.comp hg

lemma localMetricGradient_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContinuousAt g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricGradient g f) x :=
  (metric_inverse_continuousAt g x hg hp).clm_apply (hf.continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

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

local instance instFactEqNatFinrankRealAmbientBaseHAddOfNat_5_r245269_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r245269_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

lemma seedEigenvalue_pos {N : ℕ} (hN : 0 < N) : 0 < seedEigenvalue N := by
  unfold seedEigenvalue
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogarithmicBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_r245269_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedLogDomain_open : IsOpen seedLogDomain :=
  Complex.isOpen_slitPlane.preimage seedQuadratic_contDiff.continuous

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seedChartAmbient_smooth : ContDiff ℝ ∞ seedChartAmbient := by
  rw [show seedChartAmbient = stereoInvFunAux (-(seedPoint : SeedAmbient)) ∘ centeredSphereIsometry seedPoint from
    centeredSphereChart_inverse seedPoint]
  exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry seedPoint).contDiff

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientMetricJets
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

lemma coefficientMetricValue_smoothAt (c : CoefficientPoint E)
    (e : (E →L[ℝ] ℝ) ≃L[ℝ] E) (he : e.toContinuousLinearMap = c.1) :
    ContDiffAt ℝ ∞ (coefficientMetricValue : CoefficientPoint E → E →L[ℝ] E →L[ℝ] ℝ) c := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse c.1 := by
    rw [← he]; exact contDiffAt_map_inverse e
  exact contDiffAt_snd.smul (hi.comp c contDiffAt_fst)

end
end Yau.Geometry

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

lemma coefficientMetric_symmetric (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α))
    (hs : ∀ α β : E →L[ℝ] ℝ, α (c.1 β) = β (c.1 α)) (u v : E) :
    coefficientMetricValue c u v = coefficientMetricValue c v u := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have hh := hs (e.symm u) (e.symm v)
  change e.symm u (e (e.symm v)) = e.symm v (e (e.symm u)) at hh
  rw [e.apply_symm_apply,e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using congrArg (fun z : ℝ ↦ c.2*z) hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedCoordMetricRegularity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seedCoordMetric_smooth (c : BaseModel → CoefficientPoint BaseModel)
    (hc : ContDiff ℝ ∞ c)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α)) :
    ContDiff ℝ ∞ (seedCoordMetric c) := by
  have hm : ContDiff ℝ ∞ (coefficientMetricValue ∘ c) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (coefficientMetricValue_smoothAt (c y) (positiveContravariantEquiv (c y).1 (hp y)) rfl).comp y hc.contDiffAt
  have hh := (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap.precomp ℝ)).clm_comp
    ((hm.comp seedCoordEquiv.contDiff).clm_comp
      (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  ext u v
  rfl

lemma seedCoordMetric_positive (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hρ : ∀ y, 0 < (c y).2) (x : _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) (hv : v ≠ 0) :
    0 < seedCoordMetric c x v v :=
  linearMetricField_positive seedCoordEquiv (coefficientMetricValue ∘ c) x
    (coefficientMetric_positive (c (seedCoordEquiv x)) (hp _) (hρ _)) v hv

lemma seedCoordMetric_symmetric (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hs : ∀ y (α β : BaseModel →L[ℝ] ℝ), α ((c y).1 β) = β ((c y).1 α))
    (x u v : _root_.OAI.Yau.Jets.Coord) : seedCoordMetric c x u v = seedCoordMetric c x v u :=
  coefficientMetric_symmetric (c (seedCoordEquiv x)) (hp _) (hs _) _ _

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

lemma metricGradient_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    metricGradient g S =ᶠ[𝓝 x] metricGradient G A := by
  filter_upwards [hg,hS.fderiv (𝕜 := ℝ)] with z hz hd
  simp only [metricGradient,hz,hd]

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

lemma intrinsicChartCoefficient_pair (A : IntrinsicTensor) (ρ : Base → ℝ)
    (p : Base) (z : BaseModel) (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) =
      A ((extChartAt (𝓡 4) p).symm z)
        (sphereCoordinateCovector p z (baseCovectorCoordinates α))
        (sphereCoordinateCovector p z (baseCovectorCoordinates β)) := by
  change α (matrixContravariant _ β) = _
  rw [matrixContravariant_pair,intrinsicSphereChartTensor_eq,intrinsicAmbientMatrix_chart_pairing]

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

include hs in
lemma intrinsicChartCoefficient_symmetric (ρ : Base → ℝ) (p : Base) (z : BaseModel)
    (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) = β ((intrinsicChartCoefficient A ρ p z).1 α) := by
  rw [intrinsicChartCoefficient_pair,intrinsicChartCoefficient_pair,hs]

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

lemma seedCoordBranch_open : IsOpen seedCoordBranch :=
  seedLogDomain_open.preimage (seedChartAmbient_smooth.continuous.comp seedCoordEquiv.continuous)

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_FiniteSphereCoefficientAtlas
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
local instance sphereCoefficientAtlasDim : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma finiteAtlas_sphereChartCoordMap_isOpenMap (p : Base) : IsOpenMap (sphereChartCoordMap p) := by
  intro U hU
  have he : sphereChartCoordMap p '' U =
      (extChartAt (𝓡 4) p).symm '' (seedCoordEquiv '' U) := (image_image ((extChartAt (𝓡 4) p).symm) seedCoordEquiv U).symm
  rw [he]
  change IsOpen ((stereographic' 4 (-p)).symm '' (seedCoordEquiv '' U))
  exact (stereographic' 4 (-p)).isOpen_image_symm_of_subset_target
    (seedCoordEquiv.isOpenMap U hU) (by simp)

lemma finiteAtlas_sphereChartCoordMap_zero (p : Base) : sphereChartCoordMap p 0 = p := by
  simp only [sphereChartCoordMap,map_zero,centeredSphereChart_inverse_zero]

theorem finite_sphere_coordinate_cover :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) 1,
      sphereChartCoordMap p z = x := by
  have hcover : (univ : Set Base) ⊆ ⋃ p : Base, sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1 := by
    intro x _
    exact mem_iUnion.mpr ⟨x,0,mem_ball_self (by norm_num),finiteAtlas_sphereChartCoordMap_zero x⟩
  obtain ⟨P,hP⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Base ↦ sphereChartCoordMap p '' ball (0 : Yau.Jets.Coord) 1)
    (fun p ↦ finiteAtlas_sphereChartCoordMap_isOpenMap p _ isOpen_ball) hcover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := mem_iUnion₂.mp (hP (mem_univ x))
  exact ⟨p,hp,z,hz,hzx⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactLocalCompositionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma compact_local_derivative_power_bound (g : E → F) {U Q : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hQ : IsCompact Q) (hQU : Q ⊆ U) (J : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x ∈ Q, ∀ i, 1 ≤ i → i ≤ J →
      ‖iteratedFDeriv ℝ i g x‖ ≤ D^i := by
  have hc (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i g) Q := by
    intro x hx
    exact ((hg.contDiffAt (hU.mem_nhds (hQU hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).continuousWithinAt
  have hb (i : Fin (J+1)) : ∃ C : ℝ, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val g x‖ ≤ C :=
    hQ.exists_bound_of_continuousOn (hc i.val)
  choose C hC using hb
  let D : ℝ := max 1 (∑ i, |C i|)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D,hD,?_⟩
  intro x hx i hi hiJ
  let j : Fin (J+1) := ⟨i,by omega⟩
  have hj : C j ≤ D := (le_abs_self _).trans
    ((Finset.single_le_sum (fun k _ ↦ abs_nonneg (C k)) (Finset.mem_univ j)).trans (le_max_right _ _))
  exact (hC j x hx).trans (hj.trans (by simpa using pow_le_pow_right₀ hD hi))

theorem compact_local_composition_derivative_bound (g : E → F) {U Q : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hQ : IsCompact Q) (hQU : Q ⊆ U) (J : ℕ) :
    ∃ C > 0, ∀ (f : F → G), ContDiff ℝ ∞ f → ∀ eps : ℝ, 0 ≤ eps →
      (∀ y i, i ≤ J → ‖iteratedFDeriv ℝ i f y‖ ≤ eps) →
      ∀ x ∈ Q, ∀ i, i ≤ J → ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤ C*eps := by
  obtain ⟨D,hD,hDb⟩ := compact_local_derivative_power_bound g hU hg hQ hQU J
  refine ⟨1+(J.factorial:ℝ)*D^J,by positivity,?_⟩
  intro f hf eps heps hb x hx i hi
  have h := norm_iteratedFDerivWithin_comp_le hf.contDiffOn hg
    (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top)) uniqueDiffOn_univ hU.uniqueDiffOn
    (fun _ _ ↦ mem_univ _) (hQU hx)
    (fun k hk ↦ by simpa only [iteratedFDerivWithin_univ] using hb (g x) k (hk.trans hi))
    (fun k hk hki ↦ by
      rw [iteratedFDerivWithin_of_isOpen k hU (hQU hx)]
      exact hDb x hx k hk (hki.trans hi))
  rw [iteratedFDerivWithin_of_isOpen i hU (hQU hx)] at h
  have hfac : (i.factorial:ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hi
  have hpow : D^i ≤ D^J := pow_le_pow_right₀ hD hi
  calc
    _ ≤ (i.factorial:ℝ)*eps*D^i := h
    _ ≤ (J.factorial:ℝ)*eps*D^J := by gcongr
    _ ≤ (1+(J.factorial:ℝ)*D^J)*eps := by nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SupportedSphereChartBounds
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

theorem supported_sphere_chart_scalar_bound (r : ℝ) (p : Base)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ f : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f →
      tsupport f ⊆ seedSpherePatch r → ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ f (seedSphereFromCoord y)) x‖ ≤ eps) →
      ∀ x ∈ Q, ∀ i, i ≤ J →
        ‖iteratedFDeriv ℝ i (fun y ↦ f (sphereChartCoordMap p y)) x‖ ≤ C*eps := by
  let K : Set Yau.Jets.Coord := Q ∩ sphereChartCoordMap p ⁻¹' closure (seedSpherePatch r)
  have hK : IsCompact K := hQ.inter_right
    (isClosed_closure.preimage (sphereChartCoordMap_smooth p).continuous)
  have hKU : K ⊆ sphereChartTransitionDomain p seedPoint := by
    intro x hx
    exact seedSpherePatch_closure_in_chart r hx.2
  obtain ⟨C,hC,hcomp⟩ := compact_local_composition_derivative_bound (G := ℝ)
    (sphereChartTransition p seedPoint) (sphereChartTransitionDomain_open p seedPoint)
    (sphereChartTransition_smoothOn p seedPoint) hK hKU J
  refine ⟨C,hC,?_⟩
  intro f hf hsup eps heps hb x hx i hi
  by_cases hxs : sphereChartCoordMap p x ∈ closure (seedSpherePatch r)
  · have hxK : x ∈ K := ⟨hx,hxs⟩
    have he : (fun y ↦ f (sphereChartCoordMap p y)) =ᶠ[𝓝 x]
        (fun y ↦ f (seedSphereFromCoord y)) ∘ sphereChartTransition p seedPoint := by
      filter_upwards [(sphereChartTransitionDomain_open p seedPoint).mem_nhds (hKU hxK)] with y hy
      exact congrArg f (sphereChartTransition_point p seedPoint hy).symm
    rw [(he.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hcomp _ (hf.comp (sphereChartCoordMap_smooth seedPoint)).contDiff eps heps hb x hxK i hi
  · have hz : f =ᶠ[𝓝 (sphereChartCoordMap p x)] (fun _ ↦ 0) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hxs (subset_closure (hsup h)))
    have hz' : (fun y ↦ f (sphereChartCoordMap p y)) =ᶠ[𝓝 x] (fun _ ↦ 0) :=
      hz.comp_tendsto (sphereChartCoordMap_smooth p).continuous.continuousAt
    rw [(hz'.iteratedFDeriv ℝ i).eq_of_nhds]
    simpa using mul_nonneg hC.le heps

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma matrix_coefficient_derivative_bound
    (M : E → Matrix (Fin 4) (Fin 4) ℝ) (b : E → ℝ)
    (hM : ∀ j k, ContDiff ℝ ∞ (fun x ↦ M x j k)) (hb : ContDiff ℝ ∞ b)
    (x : E) (i : ℕ) {eps : ℝ} (heps : 0 ≤ eps)
    (hm : ∀ j k, ‖iteratedFDeriv ℝ i (fun y ↦ M y j k) x‖ ≤ eps)
    (hbnd : ‖iteratedFDeriv ℝ i b x‖ ≤ eps) :
    ‖iteratedFDeriv ℝ i (fun y ↦ (matrixContravariant (M y),b y)) x‖ ≤
      (1+∑ j, ∑ k, ‖coefficientEntryLinear j k‖)*eps := by
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  have hs (j k : Fin 4) : ContDiff ℝ ∞ (fun y ↦ coefficientEntryLinear j k (M y j k)) :=
    (hM j k).smul contDiff_const
  have hmat : ContDiff ℝ ∞ (fun y ↦ matrixContravariant (M y)) := by
    simp_rw [matrixContravariant_entry_sum]
    exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦ hs j k))
  have hbound : ‖iteratedFDeriv ℝ i (fun y ↦ matrixContravariant (M y)) x‖ ≤
      (∑ j, ∑ k, ‖coefficientEntryLinear j k‖)*eps := by
    simp_rw [matrixContravariant_entry_sum]
    rw [iteratedFDeriv_fun_sum_apply (fun j _ ↦
      (ContDiff.sum (fun k _ ↦ hs j k)).contDiffAt.of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top)))]
    refine (norm_sum_le _ _).trans ?_
    simp_rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [iteratedFDeriv_fun_sum_apply (fun k _ ↦ (hs j k).contDiffAt.of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top)))]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro k _
    change ‖iteratedFDeriv ℝ i (fun y ↦ M y j k • ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.basisFun (Fin 4) ℝ k)).smulRight (EuclideanSpace.basisFun (Fin 4) ℝ j))) x‖ ≤ _
    rw [iteratedFDeriv_smul_const_apply ((hM j k).of_le
      (by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
    exact ((coefficientEntryLinear j k).norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hm j k) (norm_nonneg _))
  rw [iteratedFDeriv_prodMk hmat.contDiffAt hb.contDiffAt (by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))]
  have hn : 0 ≤ ∑ j, ∑ k, ‖coefficientEntryLinear j k‖ :=
    Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
  rw [ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact hbound.trans (by nlinarith)
  · exact hbnd.trans (by nlinarith)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FrequencyLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma compact_real_derivative_bound (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    {Q : Set E} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ i, i ≤ r → ∀ x ∈ Q, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hb (i : Fin (r+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val f x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image (hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (i.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose c hc hbound using hb
  have hp : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨1+∑ i, c i,by linarith,?_⟩
  intro i hi x hx
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  exact (hbound ⟨i,by omega⟩ x hx).trans (by linarith)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalFrequencyLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frequency_product_derivative_on (f g : E → ℝ) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U) (r a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (_ : 0 ≤ B) (hH : 0 ≤ H) (_ : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(r+a+b)*(H*K) := by
  have hprod := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hprod
  refine hprod.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*(A*N^(i+a)*H)*
        (B*N^(r-i+b)*K) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      gcongr
      · exact hfb i hir
      · exact hgb (r-i) (by omega)
    _ = (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ))*(A*B*N^(r+a+b)*(H*K)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
      have hp : N^(i+a)*N^(r-i+b) = N^(r+a+b) := by rw [← pow_add]; congr 1; omega
      calc
        _ = (r.choose i:ℝ)*(A*B*(N^(i+a)*N^(r-i+b))*(H*K)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)) = (2:ℝ)^r := by
        exact_mod_cast (Nat.sum_range_choose r)
      rw [hc]
      ring

lemma scaled_frequency_product_on (f g : E → ℝ) {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U)
    (r s a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(s*i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(s*i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(s*r+a+b)*(H*K) := by
  have hf' (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ (A*N^a)*(N^s)^(i+0)*H := by
    convert hfb i hi using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.add_zero,pow_add,← pow_mul]
    ring
  have hg' (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i g x‖ ≤ (B*N^b)*(N^s)^(i+0)*K := by
    convert hgb i hi using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.add_zero,pow_add,← pow_mul]
    ring
  have h := frequency_product_derivative_on f g hU hf hg x hx r 0 0
    (by positivity) (by positivity) (by positivity) hH hK hf' hg'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.add_zero,pow_add,← pow_mul]
  ring

end
end Yau.Geometry

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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedDivergenceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma scaled_frequency_product (f g : Yau.Jets.Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Yau.Jets.Coord)
    (r s a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(s*i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(s*i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(s*r+a+b)*(H*K) :=
  scaled_frequency_product_on f g isOpen_univ hf.contDiffOn hg.contDiffOn x (mem_univ x)
    r s a b hN hA hB hH hK hfb hgb

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CorrectionProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem compact_multiplier_frequency_bound (q : Yau.Jets.Coord → ℝ) (hq : ContDiff ℝ ∞ q)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (v : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ v →
      ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B → ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i, i ≤ r → ‖iteratedFDeriv ℝ i v x‖ ≤ B*N^(137*i+a)) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (fun y ↦ q y*v y) x‖ ≤ C*B*N^(137*i+a) := by
  obtain ⟨G,hG,hgb⟩ := compact_real_derivative_bound q hq hQ r
  refine ⟨(2:ℝ)^r*G,by positivity,?_⟩
  intro v hv N B hN hB a x hx hb i hi
  have h := scaled_frequency_product q v hq hv x i 137 0 a (N := N) (by linarith) hG.le hB
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun j hj ↦ (hgb j (by omega) x hx).trans (by
      have hp : 1 ≤ N^(137*j+0) := one_le_pow₀ hN
      simpa using le_mul_of_one_le_right hG.le hp))
    (fun j hj ↦ by simpa using hb j (by omega))
  simp only [Nat.add_zero,mul_one] at h
  exact h.trans (by gcongr; norm_num)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicSeedRegularity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma intrinsicSeedCoordMetric_regular (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ContDiff ℝ ∞ (intrinsicSeedCoordMetric A rho) ∧
    (∀ x u v, intrinsicSeedCoordMetric A rho x u v = intrinsicSeedCoordMetric A rho x v u) ∧
    (∀ x v, v ≠ 0 → 0 < intrinsicSeedCoordMetric A rho x v v) := by
  rw [← intrinsicSeedCoordMetric_eq A hs hp rho hrp]
  let c := intrinsicChartCoefficient A rho seedPoint
  have hc : ContDiff ℝ ∞ c := contDiff_iff_contDiffAt.mpr (fun z ↦
    intrinsicChartCoefficient_smoothAt A hA hs hp rho hr seedPoint
      (by rw [centeredSphereChart_target]; trivial))
  have hcp : ∀ z (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c z).1 α) :=
    fun z ↦ intrinsicChartCoefficient_positive A hs hp rho seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  exact ⟨seedCoordMetric_smooth c hc hcp,
    seedCoordMetric_symmetric c hcp (fun z ↦ intrinsicChartCoefficient_symmetric A hs rho seedPoint z),
    seedCoordMetric_positive c hcp (fun _ ↦ hrp _)⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationOldData
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma corrugationOldSlope_continuousOn (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ContinuousOn (corrugationOldSlope g S) U := by
  intro y hy
  have hg' := hg.contDiffAt (hU.mem_nhds hy)
  have hS' := hS.contDiffAt (hU.mem_nhds hy)
  have hgrad : ContinuousAt (metricGradient g S) y :=
    localMetricGradient_continuousAt g S y hg'.continuousAt hS' (hp y hy)
  exact (Real.continuous_sqrt.continuousAt.comp
    ((hg'.continuousAt.clm_apply hgrad).clm_apply hgrad)).continuousWithinAt

end
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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_PlacedEnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma PlacedEnvelopeData.closure_U_branch {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.U ⊆ seedCoordBranch :=
  d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans
    (subset_closure.trans (d.patch_V.trans d.V_branch))))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRoundPerturbation
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
lemma roundTensorPerturbation_zero (alpha : Base → ℝ) (x : Base) (hx : x ∉ tsupport alpha) :
    roundTensorPerturbation alpha x = 0 := by
  ext v w
  simp [roundTensorPerturbation,image_eq_zero_of_notMem_tsupport hx]

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundTensorCoordinateBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma roundTensorPerturbation_seed_entry (a : Base → ℝ) (x : Yau.Jets.Coord) (j k : Fin 4) :
    intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv x) j k =
      if j=k then roundCoordFactor x*a (seedSphereFromCoord x) else 0 := by
  rw [roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp [Matrix.one_apply,seedSphereFromCoord,mul_comm]

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

lemma round_increment_entry_smooth (a : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (j k : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicSphereChartTensor (roundTensorPerturbation a)
      seedPoint (seedCoordEquiv x) j k) := by
  simp_rw [roundTensorPerturbation_seed_entry]
  split_ifs
  · exact roundCoordFactor_smooth.mul (seed_scalar_pullback_smooth a ha)
  · exact contDiff_const

lemma intrinsic_seed_increment_pullback_smooth (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicChartCoefficient (roundTensorPerturbation a) b
      seedPoint (seedCoordEquiv x)) := by
  apply ContDiff.prodMk _ (seed_scalar_pullback_smooth b hb)
  change ContDiff ℝ ∞ (fun x ↦ matrixContravariant
    (intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv x)))
  simp_rw [matrixContravariant_entry_sum]
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact ContDiff.sum (fun j _ ↦ ContDiff.sum (fun k _ ↦
    (round_increment_entry_smooth a ha j k).smul contDiff_const))

lemma intrinsic_seed_increment_smooth (A : IntrinsicTensor) (rho a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b) :
    ContDiff ℝ ∞ (fun z ↦
      intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
        (fun p ↦ rho p+b p) seedPoint z-intrinsicChartCoefficient A rho seedPoint z) := by
  simp_rw [intrinsicChartCoefficient_increment]
  have h := (intrinsic_seed_increment_pullback_smooth a b ha hb).comp seedCoordEquiv.symm.contDiff
  simpa only [Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using h

theorem intrinsic_coefficient_increment_derivative_bound (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i j k, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv y) j k) x‖ ≤ eps) →
      ∀ z i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
          (fun p ↦ rho p+b p) seedPoint y-intrinsicChartCoefficient A rho seedPoint y) z‖ ≤ C*eps := by
  let K : ℝ := 1+∑ j, ∑ k, ‖coefficientEntryLinear j k‖
  let B : ℝ := max 1 ‖seedCoordEquiv.symm.toContinuousLinearMap‖
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) ↦ norm_nonneg (coefficientEntryLinear j k)))
    dsimp [K] <;> linarith
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨K*B^J,by positivity,?_⟩
  intro A rho a b ha hb eps heps hbb hab z i hi
  let F : Yau.Jets.Coord → CoefficientPoint BaseModel := fun x ↦
    intrinsicChartCoefficient (roundTensorPerturbation a) b seedPoint (seedCoordEquiv x)
  have hF : ContDiff ℝ ∞ F := intrinsic_seed_increment_pullback_smooth a b ha hb
  have hpoint : ‖iteratedFDeriv ℝ i F (seedCoordEquiv.symm z)‖ ≤ K*eps :=
    matrix_coefficient_derivative_bound _ _ (round_increment_entry_smooth a ha)
      (seed_scalar_pullback_smooth b hb) _ i heps
      (fun j k ↦ hab _ i j k hi) (hbb _ i hi)
  simp_rw [intrinsicChartCoefficient_increment]
  have heq : intrinsicChartCoefficient (roundTensorPerturbation a) b seedPoint =
      F ∘ seedCoordEquiv.symm.toContinuousLinearMap := by
    funext y
    simp [F]
  rw [heq,seedCoordEquiv.symm.toContinuousLinearMap.iteratedFDeriv_comp_right hF z (by exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hpow : ‖seedCoordEquiv.symm.toContinuousLinearMap‖^i ≤ B^J := by
    calc
      _ ≤ B^i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      _ ≤ B^J := pow_le_pow_right₀ hB hi
  calc
    _ ≤ (K*eps)*B^J := mul_le_mul hpoint hpow (by positivity) (by positivity)
    _ = (K*B^J)*eps := by ring

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

theorem supported_sphere_coefficient_coord_bound (r : ℝ) (p : Base)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      tsupport a ⊆ seedSpherePatch r → tsupport b ⊆ seedSpherePatch r →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ a (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      ∀ x ∈ Q, ∀ i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicChartCoefficient (fun z ↦ A z+roundTensorPerturbation a z)
          (fun z ↦ rho z+b z) p (seedCoordEquiv y)-intrinsicChartCoefficient A rho p (seedCoordEquiv y)) x‖ ≤ C*eps := by
  obtain ⟨Cs,hCs,hscalar⟩ := supported_sphere_chart_scalar_bound r p hQ J
  obtain ⟨Cm,hCm,hmul⟩ := compact_multiplier_frequency_bound roundCoordFactor roundCoordFactor_smooth hQ J
  let K : ℝ := 1+∑ j, ∑ k, ‖coefficientEntryLinear j k‖
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) ↦ norm_nonneg (coefficientEntryLinear j k)))
    dsimp [K] <;> linarith
  refine ⟨K*((Cm+1)*Cs),by positivity,?_⟩
  intro A rho a b ha hb has hbs eps heps hab hbb x hx i hi
  have ha' := hscalar a ha has eps heps hab
  have hb' := hscalar b hb hbs eps heps hbb
  have hm (j k : Fin 4) : ‖iteratedFDeriv ℝ i (fun y ↦
      intrinsicSphereChartTensor (roundTensorPerturbation a) p (seedCoordEquiv y) j k) x‖ ≤ ((Cm+1)*Cs)*eps := by
    simp_rw [roundTensorPerturbation_any_entry]
    by_cases hjk : j=k
    · simp only [hjk,ite_true, if_true]
      have h := hmul (fun y ↦ a (sphereChartCoordMap p y))
        (ha.comp (sphereChartCoordMap_smooth p)).contDiff 1 (Cs*eps) (by norm_num) (by positivity) 0 x hx
        (fun k hk ↦ by simpa using ha' x hx k hk) i hi
      simp only [one_pow,mul_one] at h
      exact h.trans (by nlinarith)
    · simp only [hjk,ite_false, if_false]
      simpa using (show 0 ≤ ((Cm+1)*Cs)*eps by positivity)
  have hbnd : ‖iteratedFDeriv ℝ i (fun y ↦ b (sphereChartCoordMap p y)) x‖ ≤ ((Cm+1)*Cs)*eps :=
    (hb' x hx i hi).trans (by nlinarith [mul_nonneg hCm.le (mul_nonneg hCs.le heps)])
  simp_rw [intrinsicChartCoefficient_increment]
  have h := matrix_coefficient_derivative_bound _ _ (round_increment_any_entry_smooth a ha p)
    (hb.comp (sphereChartCoordMap_smooth p)).contDiff x i (by positivity) hm hbnd
  simpa only [K,intrinsicChartCoefficient,sphereChartCoordMap,Function.comp_def,mul_assoc] using h

theorem supported_sphere_coefficient_bound (r : ℝ) (p : Base)
    {Q : Set BaseModel} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      tsupport a ⊆ seedSpherePatch r → tsupport b ⊆ seedSpherePatch r →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ a (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      ∀ z ∈ Q, ∀ i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicChartCoefficient (fun x ↦ A x+roundTensorPerturbation a x)
          (fun x ↦ rho x+b x) p y-intrinsicChartCoefficient A rho p y) z‖ ≤ C*eps := by
  obtain ⟨C,hC,hcoord⟩ := supported_sphere_coefficient_coord_bound r p
    (hQ.image seedCoordEquiv.symm.continuous) J
  let B : ℝ := max 1 ‖seedCoordEquiv.symm.toContinuousLinearMap‖
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨C*B^J,by positivity,?_⟩
  intro A rho a b ha hb has hbs eps heps hab hbb z hz i hi
  let F : Yau.Jets.Coord → CoefficientPoint BaseModel := fun x ↦
    intrinsicChartCoefficient (roundTensorPerturbation a) b p (seedCoordEquiv x)
  have hF : ContDiff ℝ ∞ F := intrinsic_any_increment_pullback_smooth a b ha hb p
  have hpoint : ‖iteratedFDeriv ℝ i F (seedCoordEquiv.symm z)‖ ≤ C*eps := by
    simpa only [intrinsicChartCoefficient_increment] using
      hcoord A rho a b ha hb has hbs eps heps hab hbb _ ⟨z,hz,rfl⟩ i hi
  simp_rw [intrinsicChartCoefficient_increment]
  have heq : intrinsicChartCoefficient (roundTensorPerturbation a) b p =
      F ∘ seedCoordEquiv.symm.toContinuousLinearMap := by funext y; simp [F]
  rw [heq,seedCoordEquiv.symm.toContinuousLinearMap.iteratedFDeriv_comp_right hF z
    (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hpow : ‖seedCoordEquiv.symm.toContinuousLinearMap‖^i ≤ B^J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i).trans (pow_le_pow_right₀ hB hi)
  calc
    _ ≤ (C*eps)*B^J := mul_le_mul hpoint hpow (by positivity) (by positivity)
    _ = _ := by ring

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

theorem finite_sphere_coefficient_atlas :
    ∃ P : Finset Base, ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z = x := by
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  refine ⟨P,?_⟩
  intro x
  obtain ⟨p,hp,z,hz,hzx⟩ := hP x
  refine ⟨p,hp,seedCoordEquiv z,?_,hzx⟩
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset ((seedCoordEquiv.isOpenMap _ isOpen_ball).mem_nhds ⟨z,hz,rfl⟩)
    (image_mono ball_subset_closedBall)

theorem supported_finite_atlas_coefficient_bound (r : ℝ) (P : Finset Base) (J : ℕ) :
    ∃ C > 0, ∀ (A : IntrinsicTensor) (rho a b : Base → ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      tsupport a ⊆ seedSpherePatch r → tsupport b ⊆ seedSpherePatch r →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ a (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      sphereCoefficientDistance P J A rho (fun x ↦ A x+roundTensorPerturbation a x)
        (fun x ↦ rho x+b x) ≤ C*eps := by
  classical
  have hex (p : P) := supported_sphere_coefficient_bound r p sphereAtlasCore_compact J
  choose c hc hbound using hex
  let C : ℝ := 1+∑ p : P, c p
  have hsum : 0 ≤ ∑ p : P, c p := Finset.sum_nonneg (fun p _ ↦ (hc p).le)
  have hC : 0 < C := by change 0 < 1+∑ p : P, c p; linarith
  refine ⟨C,hC,?_⟩
  intro A rho a b ha hb has hbs eps heps hab hbb
  apply finiteChartDerivativeSize_le _ _ _ _ (mul_nonneg hC.le heps)
  intro p hp i hi z hz
  let q : P := ⟨p,hp⟩
  have hcC : c q ≤ C := by
    have := Finset.single_le_sum (fun p _ ↦ (hc p).le) (Finset.mem_univ q)
    change c q ≤ 1+∑ p : P, c p
    linarith
  exact (hbound q A rho a b ha hb has hbs eps heps hab hbb z hz i hi).trans
    (mul_le_mul_of_nonneg_right hcC heps)

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

theorem intrinsic_coefficient_neighborhood_preserved
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrho : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    {r delta : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ z ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient A rho seedPoint z,
        fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) z) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet z) < delta) :
    ∃ eps > 0, ∀ a b : Base → ℝ,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b →
      (∀ x i, i ≤ 1 → ‖iteratedFDeriv ℝ i (fun y ↦ b (seedSphereFromCoord y)) x‖ ≤ eps) →
      (∀ x i j k, i ≤ 1 → ‖iteratedFDeriv ℝ i (fun y ↦
        intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv y) j k) x‖ ≤ eps) →
      ∀ z ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
          (fun p ↦ rho p+b p) seedPoint z,
          fderiv ℝ (intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
            (fun p ↦ rho p+b p) seedPoint) z) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet z) < delta := by
  let c := intrinsicChartCoefficient A rho seedPoint
  have hc : ContDiff ℝ ∞ c := contDiff_iff_contDiffAt.mpr (fun z ↦
    intrinsicChartCoefficient_smoothAt A hA hs hp rho hrho seedPoint
      (by rw [centeredSphereChart_target]; trivial))
  obtain ⟨eta,heta,hmargin⟩ := coefficient_compact_strict_margin c hc hr hclose
  obtain ⟨C,hC,hbound⟩ := intrinsic_coefficient_increment_derivative_bound 1
  refine ⟨eta/(2*C),by positivity,?_⟩
  intro a b ha hb hbb hab z hz
  let d := intrinsicChartCoefficient (fun p ↦ A p+roundTensorPerturbation a p)
    (fun p ↦ rho p+b p) seedPoint
  have hdifference : ContDiff ℝ ∞ (fun y ↦ d y-c y) :=
    intrinsic_seed_increment_smooth A rho a b ha hb
  have hd : ContDiff ℝ ∞ d := by
    have h := hc.add hdifference
    simpa only [← add_sub_assoc,add_sub_cancel_left] using h
  have hinc := hbound A rho a b ha hb (eta/(2*C)) (by positivity) hbb hab
  have h0 : ‖d z-c z‖ ≤ C*(eta/(2*C)) := by
    simpa only [norm_iteratedFDeriv_zero] using hinc z 0 (by omega)
  have h1 : ‖fderiv ℝ (fun y ↦ d y-c y) z‖ ≤ C*(eta/(2*C)) := by
    simpa only [norm_iteratedFDeriv_one] using hinc z 1 (by omega)
  have hj := coefficient_firstJet_dist_le c d hc hd z h0 h1
  have he : C*(eta/(2*C)) = eta/2 := by field_simp [hC.ne']
  rw [he] at hj
  exact (dist_triangle _ ((c z,fderiv ℝ c z) : CoefficientFirstJet BaseModel) _).trans_lt
    (by have hm := hmargin z hz; linarith)

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

lemma sphereCoefficientDistance_triangle (P : Finset Base) (J : ℕ)
    (A B C : IntrinsicTensor) (rho sigma tau : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p))
    (hC : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient C tau p)) :
    sphereCoefficientDistance P J A rho C tau ≤
      sphereCoefficientDistance P J A rho B sigma+sphereCoefficientDistance P J B sigma C tau := by
  have he : (fun p z ↦ intrinsicChartCoefficient C tau p z-intrinsicChartCoefficient A rho p z) =
      (fun p z ↦ (intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)+
        (intrinsicChartCoefficient C tau p z-intrinsicChartCoefficient B sigma p z)) := by
    funext p z
    abel
  unfold sphereCoefficientDistance
  rw [he]
  exact finiteChartDerivativeSize_add_le P sphereAtlasCore_compact J _ _
    (fun p hp ↦ (hB p hp).sub (hA p hp)) (fun p hp ↦ (hC p hp).sub (hB p hp))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientNormConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

theorem sphereCoefficientDistance_mono_order (P : Finset Base) (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J K : ℕ) (hJK : J ≤ K) :
    sphereCoefficientDistance P J d.tensor d.density b.tensor b.density ≤
      sphereCoefficientDistance P K d.tensor d.density b.tensor b.density :=
  finiteChartDerivativeSize_mono_order P sphereAtlasCore_compact hJK _
    (fun p _ ↦ (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientAtlasInclusionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Target

open Manifold Yau.Geometry
open scoped ContDiff

theorem sphereCoefficientDistance_mono_atlas (P Q : Finset Base) (hPQ : P ⊆ Q)
    (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J : ℕ) : sphereCoefficientDistance P J d.tensor d.density b.tensor b.density ≤
      sphereCoefficientDistance Q J d.tensor d.density b.tensor b.density := by
  let f := fun p y ↦ intrinsicChartCoefficient b.tensor b.density p y-intrinsicChartCoefficient d.tensor d.density p y
  have hf (p : Base) : ContDiff ℝ ∞ (f p) :=
    (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
  apply finiteChartDerivativeSize_le
  · exact finiteChartDerivativeSize_nonneg Q sphereAtlasCore_compact J f (fun p _ ↦ hf p)
  · intro p hp i hi y hy
    exact norm_le_finiteChartDerivativeSize Q sphereAtlasCore_compact J f
      (fun p _ ↦ hf p) p (hPQ hp) i hi y hy

open Manifold Yau.Geometry Filter
open scoped ContDiff Topology

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignScaleContinuity
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

lemma sourceSignScale_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (sourceSignScale g S) := by
  have hgrad := metricGradient_continuous g hg hp S hS
  exact (((hg.continuous.clm_apply hgrad).clm_apply hgrad).add continuous_const).sqrt

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma source_sign_scale_eq (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ a.E) :
    sourceSignScale a.G a.A x = sourceSignScale g S x := by
  obtain ⟨hg,_,hS⟩ := a.germ x hx
  unfold sourceSignScale
  rw [hg.self_of_nhds,(metricGradient_eventuallyEq hg hS).self_of_nhds]

include a in
lemma source_sign_scale_continuousOn {H : Set _root_.OAI.Yau.Jets.Coord} (hHD : H ⊆ D) :
    ContinuousOn (sourceSignScale g S) H := by
  apply (sourceSignScale_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).continuousOn.congr
  intro x hx
  exact (a.source_sign_scale_eq x (a.centers_E (hHD hx))).symm

end LocalCompactWaveData
end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_EnvelopeNodalGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

lemma corrugationOldSlope_le_sourceSignScale
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    corrugationOldSlope g S x ≤ sourceSignScale g S x := by
  apply Real.sqrt_le_sqrt
  linarith

lemma PlacedEnvelopeData.gain_lt_sign_integral
    {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {w : _root_.OAI.Yau.Jets.Coord → ℝ}
    {r a T : ℝ} {Kset : Set _root_.OAI.Yau.Jets.Coord} {m J K k0 : ℕ}
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ x v, v ≠ 0 → 0 < g x v v) :
    T < ∫ x in seedCoordCube a, sourceSignScale g d.S x := by
  have hcube : seedCoordCube a ⊆ closure d.U := fun x hx ↦
    subset_closure (d.C_U (d.inner_C (Or.inl hx)))
  have hbranch : seedCoordCube a ⊆ seedCoordBranch := hcube.trans d.closure_U_branch
  have hi : IntegrableOn (corrugationOldSlope g d.S) (seedCoordCube a) :=  ((corrugationOldSlope_continuousOn g d.S seedCoordBranch_open hg.contDiffOn d.smooth
    (fun x _ ↦ hp x)).mono hbranch).integrableOn_compact (show IsCompact (seedCoordCube a) from isCompact_Icc)
  have hj : IntegrableOn (sourceSignScale g d.S) (seedCoordCube a) :=  (b.source_sign_scale_continuousOn hcube).integrableOn_compact
    (show IsCompact (seedCoordCube a) from isCompact_Icc)
  exact d.gain.trans_le (setIntegral_mono_on hi hj measurableSet_Icc
    (fun x _ ↦ corrugationOldSlope_le_sourceSignScale g d.S x))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicPackedQuantitativeCertificateGain
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

theorem intrinsic_packed_quantitative_certificate_gain :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (d : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density),
        (∀ y ∈ closedBall (0 : BaseModel) r,
          dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
            fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
            (roundCoefficientJet y) < δ) →
        ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
        (∀ x ∉ K, ∀ v w : AmbientBase,
          ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) →
        (∀ x ∉ K, d.density x=1) →
        ∀ L > 0, ∀ T > 0, ∀ (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps → ∀ n₀ : ℕ,
          ∃ n : ℕ, n₀ ≤ n ∧ 0 < n ∧
            ∃ (d' : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d'.density),
              sphereCoefficientDistance P J d.tensor d.density d'.tensor d'.density < eps ∧
              (∀ y ∈ closedBall (0 : BaseModel) r,
                dist ((intrinsicChartCoefficient d'.tensor d'.density seedPoint y,
                  fderiv ℝ (intrinsicChartCoefficient d'.tensor d'.density seedPoint) y) : CoefficientFirstJet BaseModel)
                  (roundCoefficientJet y) < δ) ∧
              ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
                (∀ x ∉ K', ∀ v w : AmbientBase,
                  ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
                  d'.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
                (∀ x ∉ K', d'.density x=1) ∧
                ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
                  (∀ p y, -intrinsicWeightedChartOperator d'.tensor d'.density u p y =
                    seedEigenvalue n*u ((extChartAt (𝓡 4) p).symm y)) ∧
                  ∃ (S : Yau.Jets.Coord → ℝ) (U : Set Yau.Jets.Coord) (M : ℝ),
                    0 < M ∧ 8*(n:ℝ)*L*T < M ∧ U ⊆ seedCoordPatch r ∧
                    LiteralNodalCertificate (intrinsicSeedCoordMetric d.tensor d.density)
                      S (seedCoordCube a) U n (fun x ↦ u (seedSphereFromCoord x)) M := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_global_sphere_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro d hd hclose K hK hKP hA hrho L hL T hT P J eps heps n₀
  obtain ⟨eta,heta,hpres⟩ := intrinsic_coefficient_neighborhood_preserved
    d.tensor d.smooth d.symm d.pos d.density hd hr.le hclose
  obtain ⟨Cf,hCf,hbound⟩ := supported_finite_atlas_coefficient_bound r P J
  let e : ℝ := min eta (eps/Cf)/2
  have he : 0 < e := by dsimp [e] <;> positivity
  have heeta : e ≤ eta := by have := min_le_left eta (eps/Cf); dsimp [e] <;> linarith
  have hCfe : Cf*e < eps := by
    have h := min_le_right eta (eps/Cf)
    have hdv : 0 < eps/Cf := div_pos heps hCf
    have he' : e < eps/Cf := by dsimp [e] <;> linarith
    simpa [mul_comm] using (lt_div_iff₀ hCf).mp he'
  obtain ⟨c,hc,cn,hcn,hstage⟩ := hstage d.tensor d.smooth d.symm d.pos d.density hd d.positive
    hclose K hK hKP hA hrho
  let Tg := 8*L*T/c+1
  have hTg : 0 < Tg := by dsimp [Tg] <;> positivity
  obtain ⟨w,b,hb,C,hC,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,hselect⟩ := hstage Tg (max J 1)
  obtain ⟨n,hn,hnSmall,hnlarge,hn0⟩ := (hselect.and ((eventually_inverse_square_small C e he).and
    ((eventually_ge_atTop n₀).and (eventually_gt_atTop (0:ℕ))))).exists
  obtain ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,hsize,heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed,htensor,hall,
    hlifts,hliftne,hlifte,hlam,hnodal,hrobust⟩ := hn
  let := hfin
  let K' := K ∪ seedSphereFromCoord '' (Q ∪ Qw)
  have hK' : IsCompact K' := hK.union ((hQ.union hQw).image seedSphereFromCoord_continuous)
  have hK'P : K' ⊆ seedSpherePatch r := by
    rintro x (hx | ⟨y,hy,rfl⟩)
    · exact hKP hx
    · have hyΩ : y ∈ w.Ω := hy.elim (fun h ↦ hQΩ h) (fun h ↦ hQwΩ h)
      exact ⟨seedCoordEquiv y,w.closure_Ω_patch (subset_closure hyΩ),rfl⟩
  have haK : tsupport ag ⊆ K' := hags.trans ((image_mono subset_union_left).trans subset_union_right)
  have hbK : tsupport bg ⊆ K' := hbgs.trans ((image_mono subset_union_left).trans subset_union_right)
  have hscalar : ∀ x i, i ≤ max J 1 →
      ‖iteratedFDeriv ℝ i (fun y ↦ ag (seedSphereFromCoord y)) x‖ +
      ‖iteratedFDeriv ℝ i (fun y ↦ bg (seedSphereFromCoord y)) x‖ < e := by
    intro x i hi
    simp_rw [hagval,hbgval]
    exact (hsize x i hi).trans_lt hnSmall
  have hagb : ∀ x i, i ≤ max J 1 →
      ‖iteratedFDeriv ℝ i (fun y ↦ ag (seedSphereFromCoord y)) x‖ ≤ e := by
    intro x i hi
    have h := hscalar x i hi
    have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun y ↦ bg (seedSphereFromCoord y)) x)
    linarith
  have hbgb : ∀ x i, i ≤ max J 1 →
      ‖iteratedFDeriv ℝ i (fun y ↦ bg (seedSphereFromCoord y)) x‖ ≤ e := by
    intro x i hi
    have h := hscalar x i hi
    have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun y ↦ ag (seedSphereFromCoord y)) x)
    linarith
  let d' : SphereEnergyData := ⟨_,hnew,hnewSym,hnewPos,_,hrnew.continuous,hrnewPos⟩
  refine ⟨n,hnlarge,hn0,d',hrnew,?_,?_,K',hK',subset_union_left,hK'P,?_,?_,
    ug,hug,hugne,hall,?_⟩
  · exact (hbound d.tensor d.density ag bg hag hbg (haK.trans hK'P) (hbK.trans hK'P)
      e he.le (fun x i hi ↦ hagb x i (hi.trans (le_max_left _ _)))
      (fun x i hi ↦ hbgb x i (hi.trans (le_max_left _ _)))).trans_lt hCfe
  · exact hpres ag bg hag hbg
      (fun x i hi ↦ (hbgb x i (hi.trans (le_max_right _ _))).trans heeta)
      (fun x i j k hi ↦ ((htensor x i j k (hi.trans (le_max_right _ _))).trans hnSmall.le).trans heeta)
  · intro x hx v z hv hz
    change (d.tensor x+roundTensorPerturbation ag x) _ _ = _
    rw [roundTensorPerturbation_zero ag x (fun h ↦ hx (haK h)),add_zero]
    exact hA x (fun h ↦ hx (Or.inl h)) v z hv hz
  · intro x hx
    change d.density x+bg x=1
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hbK h)),add_zero]
    exact hrho x (fun h ↦ hx (Or.inl h))
  · have hreg := intrinsicSeedCoordMetric_regular d.tensor d.smooth d.symm d.pos d.density hd d.positive
    have hgain := w.gain_lt_sign_integral b hreg.1 hreg.2.2
    let I := ∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric d.tensor d.density) w.S x
    have hI : 0 < I := hTg.trans hgain
    have hnreal : (0:ℝ) < n := by exact_mod_cast hn0
    refine ⟨w.S,w.U,c*((n:ℝ)*I),mul_pos hc (mul_pos hnreal hI),?_,?_,?_⟩
    · have hh := mul_lt_mul_of_pos_left hgain hc
      have heq : c*Tg=8*L*T+c := by dsimp [Tg]; field_simp
      rw [heq] at hh
      have hh' : 8*L*T < c*I := by change 8*L*T+c < c*I at hh; linarith
      have hn' := mul_lt_mul_of_pos_left hh' hnreal
      nlinarith only [hn']
    · exact subset_closure.trans (w.closure_U_Ω.trans (subset_closure.trans w.closure_Ω_patch))
    · simpa only [hugval] using hpacking

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_SeedWindowNodalLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ENNReal
noncomputable section

lemma seed_window_sqrt_bound {n : ℕ} (hn : 0 < n) {lam : ℝ}
    (hlam : lam ≤ 2*seedEigenvalue n) : Real.sqrt lam ≤ 8*(n:ℝ) := by
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · unfold seedEigenvalue at hlam
    nlinarith

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_QuantitativeCertificateNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ENNReal
noncomputable section

theorem quantitative_certificate_window_ratio {n : ℕ} (hn : 0 < n)
    {L T M mu : ℝ} (hL : 0 < L) (hT : 0 < T) (hgain : 8*(n:ℝ)*L*T < M)
    (hmu : 0 < mu) (hupper : mu ≤ 2*seedEigenvalue n)
    {m : ℝ≥0∞} (hm : ENNReal.ofReal (M/L) ≤ m) :
    ENNReal.ofReal T < m / ENNReal.ofReal (Real.sqrt mu) := by
  have hs := Real.sqrt_pos.mpr hmu
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hs)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.ofReal_mul hT.le]
  apply ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hT.le hs.le)).mpr ?_).trans_le hm
  apply (lt_div_iff₀ hL).mpr
  have hbound := mul_le_mul_of_nonneg_left (seed_window_sqrt_bound hn hupper) hT.le
  have hbound' := mul_le_mul_of_nonneg_right hbound hL.le
  nlinarith only [hbound',hgain]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicOneStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal NNReal
noncomputable section

theorem intrinsic_one_step_oai :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (d : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density),
        (∀ y ∈ closedBall (0 : BaseModel) r,
          dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
            fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
            (roundCoefficientJet y) < δ) →
        ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
        (∀ x ∉ K, ∀ v w : AmbientBase,
          ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) →
        (∀ x ∉ K, d.density x=1) →
        ∀ T > 0, ∀ (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps → ∀ n₀ : ℕ,
          ∃ n : ℕ, n₀ ≤ n ∧ 0 < n ∧
            ∃ (d' : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d'.density),
              sphereCoefficientDistance P J d.tensor d.density d'.tensor d'.density < eps ∧
              (∀ y ∈ closedBall (0 : BaseModel) r,
                dist ((intrinsicChartCoefficient d'.tensor d'.density seedPoint y,
                  fderiv ℝ (intrinsicChartCoefficient d'.tensor d'.density seedPoint) y) : CoefficientFirstJet BaseModel)
                  (roundCoefficientJet y) < δ) ∧
              ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
                (∀ x ∉ K', ∀ v w : AmbientBase,
                  ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
                  d'.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
                (∀ x ∉ K', d'.density x=1) ∧
                ∃ (P' : Finset Base) (eta : ℝ), 0 < eta ∧
                  ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
                    sphereCoefficientDistance P' 8 d'.tensor d'.density b.tensor b.density < eta →
                    ∃ (mu : ℝ) (v : Base → ℝ), mu ∈ Icc (seedEigenvalue n/2) (2*seedEigenvalue n) ∧
                      0 < mu ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
                      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
                        mu*v ((extChartAt (𝓡 4) p).symm y)) ∧
                      ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
                      (∀ x : Manifold5, -chartLaplacian
                        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                        (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
                          mu*circleLift v x) ∧
                      ENNReal.ofReal T < nodalMeasure
                        (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                        (circleLift v) / ENNReal.ofReal (Real.sqrt mu) := by
  classical
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,Hgain⟩ := intrinsic_packed_quantitative_certificate_gain
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro d hd hclose K hK hKP hA hrho T hT P J eps heps n₀
  obtain ⟨P₀,hP₀⟩ := finite_sphere_coefficient_atlas
  have hcover : ∀ x : Base, ∃ p ∈ P₀, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hx⟩ := hP₀ x
    exact ⟨p,hp,y,interior_subset hy,hx⟩
  obtain ⟨delta,hdelta,C,hC,Hpersist⟩ := sphere_reference_literal_nodal_persistence P₀ hcover d hd
    (seedCoordPatch_compactClosure r)
  let e : ℝ := min eps delta/3
  have he : 0 < e := by dsimp [e] <;> positivity
  have heps' : 2*e < eps := by have := min_le_left eps delta; dsimp [e] <;> linarith
  have hdelta' : 2*e < delta := by have := min_le_right eps delta; dsimp [e] <;> linarith
  let Pbig := P ∪ P₀
  have hC4 : 0 < (C:ℝ)^4 := by positivity
  obtain ⟨n,hnlarge,hn0,d₁,hd₁,hdist₁,hclose₁,K₁,hK₁,hKK₁,hK₁P,hA₁,hrho₁,
    u,hu,hu0,heq,S,U,M,hM,hgain,hUP,hcert⟩ :=
    Hgain d hd hclose K hK hKP hA hrho ((C:ℝ)^4) hC4 T hT Pbig J e he n₀
  have hlam : 0 < seedEigenvalue n := seedEigenvalue_pos hn0
  obtain ⟨d₂,hd₂,hdist₂,hclose₂,K₂,hK₂,hK₁K₂,hK₂P,hA₂,hrho₂,heq₂,hsimple⟩ :=
    sphere_simplicity_in_comparison_neighborhood d₁ hd₁ hr hclose₁ K₁ hK₁ hK₁P hA₁ hrho₁
      u hu hu0 (seedEigenvalue n) hlam heq Pbig J e he
  have htriangle := sphereCoefficientDistance_triangle Pbig J d.tensor d₁.tensor d₂.tensor
    d.density d₁.density d₂.density
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d₁.tensor d₁.smooth d₁.symm d₁.pos d₁.density hd₁ p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d₂.tensor d₂.smooth d₂.symm d₂.pos d₂.density hd₂ p)
  have hdist : sphereCoefficientDistance Pbig J d.tensor d.density d₂.tensor d₂.density < 2*e := by linarith
  have hdistP := (sphereCoefficientDistance_mono_atlas P Pbig Finset.subset_union_left d d₂ hd hd₂ J).trans_lt hdist
  have hdist₀ : sphereCoefficientDistance P₀ 0 d.tensor d.density d₂.tensor d₂.density < delta :=
    (sphereCoefficientDistance_mono_order P₀ d d₂ hd hd₂ 0 J (Nat.zero_le _)).trans_lt
      (((sphereCoefficientDistance_mono_atlas P₀ Pbig Finset.subset_union_right d d₂ hd hd₂ J).trans_lt hdist).trans hdelta')
  obtain ⟨N,hN,P',hP',eta,heta,Heta⟩ := Hpersist d₂ hd₂ hdist₀ u hu hu0 (seedEigenvalue n) hlam
    heq₂ hsimple (intrinsicSeedCoordMetric d.tensor d.density) S (seedCoordCube a) U n M
    (hUP.trans subset_closure) hcert
  refine ⟨n,hnlarge,hn0,d₂,hd₂,hdistP.trans heps',hclose₂,K₂,hK₂,hKK₁.trans hK₁K₂,hK₂P,
    hA₂,hrho₂,P',eta,heta,?_⟩
  intro b hb hdistb
  obtain ⟨hwindow,v,hv,hv0,hve,hlift,hln,hle,hm⟩ := Heta b hb hdistb
  have hmu : 0 < sphereIndexedEigenvalue b N := (half_pos hlam).trans_le hwindow.1
  exact ⟨sphereIndexedEigenvalue b N,v,hwindow,hmu,hv,hv0,hve,hlift,hln,hle,
    quantitative_certificate_window_ratio hn0 hC4 hT hgain hmu hwindow.2 hm⟩

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_one_step_oai := @OAI.Yau.Target.intrinsic_one_step_oai
