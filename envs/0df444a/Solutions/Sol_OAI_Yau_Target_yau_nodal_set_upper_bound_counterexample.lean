-- Prove2me | solution 1 for OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:28.39072+00:00
-- url     : https://prove2.me/submissions/dedc440a-cb77-4af9-ba8b-4d627b0d1230

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
import Mathlib.Analysis.Normed.Group.InfiniteSum
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_intrinsic_one_step

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

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

lemma finiteChartDerivativeSize_zero (P : Finset I) {Q : Set E} (hQ : IsCompact Q) (J : ℕ) :
    finiteChartDerivativeSize P Q J (fun _ _ ↦ (0:F)) = 0 := by
  apply le_antisymm
  · exact finiteChartDerivativeSize_le P Q J _ le_rfl (by intros; simp)
  · exact finiteChartDerivativeSize_nonneg P hQ J _ (fun _ _ ↦ contDiff_const)

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothBilinearPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma bilinearPullback_apply (B : W →L[ℝ] W →L[ℝ] ℝ) (T : F →L[ℝ] W) (v w : F) :
    bilinearPullback B T v w = B (T v) (T w) := rfl

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

lemma sphereWeightedChartMatrix_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (p : Base) (y : BaseModel) (i j : Fin 4) :
    sphereWeightedChartMatrix A rho p y i j =
      ambientMatrixForm (weightedBaseMatrix A rho)
        (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
        (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j)) := by
  rw [ambientMatrixForm_dot]
  unfold sphereWeightedChartMatrix
  rw [Matrix.mul_assoc]
  simp only [mul_apply,transpose_apply,
    sphereChartFrame_apply,mulVec,dotProduct]

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientMap
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MatrixMetricPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

lemma matrixCovariant_eq_of_entries (B : Matrix (Fin 4) (Fin 4) ℝ)
    (g : BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ)
    (he : ∀ i j, g (EuclideanSpace.basisFun (Fin 4) ℝ j)
      (EuclideanSpace.basisFun (Fin 4) ℝ i) = B i j) : matrixCovariant B = g := by
  ext v w
  rw [matrixCovariant_apply]
  have hv := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  have hw := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr w
  conv_rhs => rw [← hv,← hw]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,he]
  simp only [mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm,mul_assoc]

lemma matrixCovariant_horizontal (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (ρ : ℝ) (hρ : 0 < ρ) (p : Base) (z : BaseModel) :
    matrixCovariant (sphereWeightedChartMatrix A ρ p z) =
      bilinearPullback (ambientMatrixForm (weightedBaseMatrix A ρ)) (sphereChartDerivative p z) := by
  apply matrixCovariant_eq_of_entries
  intro i j
  rw [bilinearPullback_apply,ambientMatrixForm_symm _ (weightedBaseMatrix_posDef hA hρ).1,
    sphereWeightedChartMatrix_apply]

lemma matrixCovariant_round (p : Base) (z : BaseModel) :
    matrixCovariant (sphereRoundChartMatrix p z) = roundChartMetric p z := by
  have h := matrixCovariant_horizontal (1 : Matrix (Fin 5) (Fin 5) ℝ) PosDef.one 1 zero_lt_one p z
  have hm : sphereWeightedChartMatrix (1 : Matrix (Fin 5) (Fin 5) ℝ) 1 p z = sphereRoundChartMatrix p z := by
    simp [sphereWeightedChartMatrix,sphereRoundChartMatrix,weightedBaseMatrix]
  rw [hm] at h
  have hform : ambientMatrixForm (weightedBaseMatrix (1 : Matrix (Fin 5) (Fin 5) ℝ) 1) =
      ambientRoundBilinear := by
    simp only [weightedBaseMatrix,inv_one,one_smul]
    ext v w
    rw [ambientMatrixForm_dot,one_mulVec]
    change WithLp.ofLp v ⬝ᵥ WithLp.ofLp w = ⟪v,w⟫
    simp [PiLp.inner_apply,dotProduct,mul_comm]
  rw [hform] at h
  exact h

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundSphereEnergyData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Matrix Set Metric
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundSphereEnergyData_density_smooth :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ roundSphereEnergyData.density := contMDiff_const

lemma roundSphereEnergyData_coefficient :
    intrinsicChartCoefficient roundSphereEnergyData.tensor roundSphereEnergyData.density seedPoint =
      roundCoefficients := by
  funext z
  apply Prod.ext
  · change matrixContravariant (intrinsicSphereChartTensor roundCotangentTensor seedPoint z) =
      ContinuousLinearMap.inverse (roundChartMetric seedPoint z)
    rw [roundCotangentTensor_chart,← matrixCovariant_round]
    symm
    have hA : IsUnit (sphereRoundChartMatrix seedPoint z).det := isUnit_iff_ne_zero.mpr
      (sphereRoundChartMatrix_posDef seedPoint (by rw [centeredSphereChart_target]; trivial)).det_pos.ne'
    apply ContinuousLinearMap.inverse_eq
    · ext alpha v
      have h : baseCovectorCoordinates (matrixCovariant (sphereRoundChartMatrix seedPoint z)
          (matrixContravariant (sphereRoundChartMatrix seedPoint z)⁻¹ alpha)) = baseCovectorCoordinates alpha := by
        rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
          mul_nonsing_inv _ hA,one_mulVec]
      exact congrArg (fun beta : BaseModel →L[ℝ] ℝ ↦ beta v) (baseCovectorCoordinates_injective h)
    · ext v i
      change (matrixContravariant (sphereRoundChartMatrix seedPoint z)⁻¹
        (matrixCovariant (sphereRoundChartMatrix seedPoint z) v)) i = v i
      have h := matrixContravariant_coordinates (sphereRoundChartMatrix seedPoint z)⁻¹
        (matrixCovariant (sphereRoundChartMatrix seedPoint z) v)
      rw [matrixCovariant_coordinates,mulVec_mulVec,nonsing_inv_mul _ hA,one_mulVec] at h
      exact congrFun h i
  · rfl

lemma roundSphereEnergyData_comparison (r : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient roundSphereEnergyData.tensor roundSphereEnergyData.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient roundSphereEnergyData.tensor roundSphereEnergyData.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta := by
  intro y _
  simpa only [roundSphereEnergyData_coefficient,roundCoefficientJet,dist_self] using hdelta

lemma roundSphereEnergyData_exterior :
    (∀ x ∉ (∅ : Set Base), ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
      roundSphereEnergyData.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
    (∀ x ∉ (∅ : Set Base), roundSphereEnergyData.density x=1) :=
  ⟨fun x _ v w hv hw ↦ roundCotangentTensor_tangent x v w hv hw,fun _ _ ↦ rfl⟩

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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereLocalLimitGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Filter Set Yau.Geometry
open scoped ContDiff Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sphere_local_limit_gluing (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z = x)
    (w : ℕ → Base → F)
    (hlim : ∀ p ∈ P, ∃ f : BaseModel → F,
      ContDiffOn ℝ ∞ f (interior sphereAtlasCore) ∧
      ∀ z ∈ interior sphereAtlasCore,
        Tendsto (fun n ↦ w n ((extChartAt (𝓡 4) p).symm z)) atTop (𝓝 (f z))) :
    ∃ v : Base → F, ContMDiff (𝓡 4) 𝓘(ℝ,F) ∞ v ∧
      ∀ x, Tendsto (fun n ↦ w n x) atTop (𝓝 (v x)) := by
  classical
  choose f hf ht using (fun p : P ↦ hlim p.val p.property)
  have hex (x : Base) : ∃ p : P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p.val).symm z = x := by
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨⟨p,hp⟩,z,hz,he⟩
  choose c z hz he using hex
  let v : Base → F := fun x ↦ f (c x) (z x)
  have hv (x : Base) : Tendsto (fun n ↦ w n x) atTop (𝓝 (v x)) := by
    simpa only [he,v] using ht (c x) (z x) (hz x)
  have hvchart (p : P) (y : BaseModel) (hy : y ∈ interior sphereAtlasCore) :
      v ((extChartAt (𝓡 4) p.val).symm y) = f p y :=
    tendsto_nhds_unique (hv _) (ht p y hy)
  refine ⟨v,?_,hv⟩
  intro x
  have htarget : z x ∈ (extChartAt (𝓡 4) (c x).val).target := by
    rw [centeredSphereChart_target]; trivial
  have hsource : x ∈ (extChartAt (𝓡 4) (c x).val).source := by
    simpa only [he x] using (extChartAt (𝓡 4) (c x).val).map_target htarget
  have hcoord : (extChartAt (𝓡 4) (c x).val) x = z x := by
    simpa only [he x] using (extChartAt (𝓡 4) (c x).val).right_inv htarget
  have hchart := contMDiffAt_extChartAt' (I := 𝓡 4) (n := ∞)
    (x := (c x).val) (x' := x) (by simpa only [extChartAt_source] using hsource)
  have hlocal : ContDiffAt ℝ ∞ (f (c x)) ((extChartAt (𝓡 4) (c x).val) x) := by
    rw [hcoord]
    exact (hf (c x) (z x) (hz x)).contDiffAt (isOpen_interior.mem_nhds (hz x))
  apply (hlocal.contMDiffAt.comp x hchart).congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x, (extChartAt (𝓡 4) (c x).val) y ∈ interior sphereAtlasCore :=
    hchart.continuousAt (by rw [hcoord]; exact isOpen_interior.mem_nhds (hz x))
  filter_upwards [hnear,(isOpen_extChartAt_source (c x).val).mem_nhds hsource] with y hy hs
  have h := hvchart (c x) ((extChartAt (𝓡 4) (c x).val) y) hy
  simpa only [(extChartAt (𝓡 4) (c x).val).left_inv hs,Function.comp_apply] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientAmbientReconstruction
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance coefficientReconstructionDimension : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩

lemma sphereChartAmbientCovector_rep (p : Base) (v : AmbientBase) (z : BaseModel) :
    sphereCoordinateCovector p z (baseCovectorCoordinates (sphereChartAmbientCovector p v z)) =
      sphereCovectorRestriction ((extChartAt (𝓡 4) p).symm z) v := by
  symm
  apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
  intro w
  exact baseCovectorCoordinates_apply (sphereChartAmbientCovector p v z) (WithLp.toLp 2 w)

lemma sphereChartAmbientCovector_smooth (p : Base) (v : AmbientBase) :
    ContDiff ℝ ∞ (sphereChartAmbientCovector p v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact contDiffAt_const.clm_comp
    (sphereChartDerivative_smooth_at p (by rw [centeredSphereChart_target]; trivial))

lemma coefficientAmbientEntry_intrinsic (A : IntrinsicTensor) (rho : Base → ℝ)
    (p : Base) (i j : Fin 5) (z : BaseModel) :
    coefficientAmbientEntry p (intrinsicChartCoefficient A rho p) i j z =
      intrinsicAmbientMatrix A ((extChartAt (𝓡 4) p).symm z) i j := by
  unfold coefficientAmbientEntry
  rw [intrinsicChartCoefficient_pair,sphereChartAmbientCovector_rep,sphereChartAmbientCovector_rep]
  simp only [intrinsicAmbientMatrix,ambientFormMatrix,intrinsicAmbientForm_apply,
    EuclideanSpace.inner_basisFun_real]

lemma coefficientAmbientEntry_smoothOn (p : Base)
    (c : BaseModel → CoefficientPoint BaseModel) {S : Set BaseModel}
    (hc : ContDiffOn ℝ ∞ c S) (i j : Fin 5) :
    ContDiffOn ℝ ∞ (coefficientAmbientEntry p c i j) S := by
  have hcoord : ContDiff ℝ ∞ (fun z ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase)) :=
    contDiff_iff_contDiffAt.mpr (fun z ↦ smooth_inverse_chart_comp
      (Subtype.val : Base → AmbientBase) (contMDiff_coe_sphere (n := 4)) p
      (by rw [centeredSphereChart_target]; trivial))
  have hi : ContDiff ℝ ∞ (fun z ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) i) :=
    (contDiff_piLp_apply 2).comp hcoord
  have hj : ContDiff ℝ ∞ (fun z ↦ ((extChartAt (𝓡 4) p).symm z : AmbientBase) j) :=
    (contDiff_piLp_apply 2).comp hcoord
  exact ((sphereChartAmbientCovector_smooth p _).contDiffOn.clm_apply
    (hc.fst.clm_apply (sphereChartAmbientCovector_smooth p _).contDiffOn)).add
    (hi.contDiffOn.mul hj.contDiffOn)

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

lemma sphereCoefficientDistance_self (P : Finset Base) (J : ℕ) (A : IntrinsicTensor) (rho : Base → ℝ) :
    sphereCoefficientDistance P J A rho A rho = 0 := by
  simp only [sphereCoefficientDistance,sub_self]
  exact finiteChartDerivativeSize_zero P sphereAtlasCore_compact J

lemma sphereCoefficientDistance_nonneg (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p)) :
    0 ≤ sphereCoefficientDistance P J A rho B sigma :=
  finiteChartDerivativeSize_nonneg P sphereAtlasCore_compact J _ (fun p hp ↦ (hB p hp).sub (hA p hp))

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactContravariantComparison
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Yau.Jets
noncomputable section
variable {T E : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_contravariant_margin (c : T → CoefficientPoint E) (hc : Continuous c)
    (hp : ∀ t (alpha : E →L[ℝ] ℝ), alpha ≠ 0 → 0 < alpha ((c t).1 alpha))
    (hr : ∀ t, 0 < (c t).2) :
    ∃ m > 0, (∀ t (alpha : E →L[ℝ] ℝ), m*‖alpha‖^2 ≤ alpha ((c t).1 alpha)) ∧ ∀ t, m ≤ (c t).2 := by
  have hcont : Continuous (fun z : T × (E →L[ℝ] ℝ) ↦ z.2 ((c z.1).1 z.2)) :=
    continuous_snd.clm_apply ((hc.fst.comp continuous_fst).clm_apply continuous_snd)
  obtain ⟨a,ha,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0 : E →L[ℝ] ℝ) 1)) _ hcont.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hco (t : T) (alpha : E →L[ℝ] ℝ) : a*‖alpha‖^2 ≤ alpha ((c t).1 alpha) := by
    by_cases hz : alpha=0
    · simp [hz]
    have hn : 0 < ‖alpha‖ := norm_pos_iff.mpr hz
    have hu : ‖(‖alpha‖⁻¹:ℝ) • alpha‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (t,(‖alpha‖⁻¹:ℝ) • alpha)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
    simp only [map_smul,smul_apply,smul_eq_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖alpha‖)
    have he : ‖alpha‖^2*(‖alpha‖⁻¹*(‖alpha‖⁻¹*alpha ((c t).1 alpha))) =
        alpha ((c t).1 alpha) := by field_simp
    rw [he] at hmul
    nlinarith
  obtain ⟨b,hb,_,_,hbr⟩ := compact_positive_bounds isCompact_univ _ hc.snd.continuousOn
    (fun t _ ↦ hr t)
  exact ⟨min a b,lt_min ha hb,
    fun t alpha ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖alpha‖)).trans (hco t alpha),
    fun t ↦ (min_le_right _ _).trans (hbr t (mem_univ t)).1⟩

omit [FiniteDimensional ℝ E] in
lemma coefficient_relative_comparison (c d : CoefficientPoint E) {m eps : ℝ}
    (_hm : 0 < m) (heps : 0 ≤ eps)
    (hc : ∀ alpha : E →L[ℝ] ℝ, m*‖alpha‖^2 ≤ alpha (c.1 alpha)) (hr : m ≤ c.2)
    (hd : ‖d-c‖ ≤ eps*m) :
    (∀ alpha : E →L[ℝ] ℝ, |alpha (d.1 alpha)-alpha (c.1 alpha)| ≤ eps*alpha (c.1 alpha)) ∧
    |d.2-c.2| ≤ eps*c.2 := by
  have hop : ‖d.1-c.1‖ ≤ eps*m := (norm_fst_le (d-c)).trans hd
  constructor
  · intro alpha
    have hn : |alpha (d.1 alpha)-alpha (c.1 alpha)| ≤ ‖d.1-c.1‖*‖alpha‖^2 := by
      calc
        _ = ‖alpha ((d.1-c.1) alpha)‖ := by rw [sub_apply,map_sub,Real.norm_eq_abs]
        _ ≤ ‖alpha‖*‖(d.1-c.1) alpha‖ := alpha.le_opNorm _
        _ ≤ ‖alpha‖*(‖d.1-c.1‖*‖alpha‖) :=
          mul_le_mul_of_nonneg_left ((d.1-c.1).le_opNorm alpha) (norm_nonneg alpha)
        _ = _ := by ring
    exact hn.trans ((mul_le_mul_of_nonneg_right hop (sq_nonneg ‖alpha‖)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (hc alpha) heps]))
  · exact (show |d.2-c.2| ≤ eps*m by
      have h := (norm_snd_le (d-c)).trans hd
      change ‖d.2-c.2‖ ≤ eps*m at h
      rwa [Real.norm_eq_abs] at h).trans
      (mul_le_mul_of_nonneg_left hr heps)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientFormComparison
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
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma sphere_finite_atlas_coercivity (P : Finset Base)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ m > 0, ∀ p ∈ P, ∀ z ∈ sphereAtlasCore,
      (∀ alpha : BaseModel →L[ℝ] ℝ,
        m*‖alpha‖^2 ≤ alpha ((intrinsicChartCoefficient A rho p z).1 alpha)) ∧
      m ≤ (intrinsicChartCoefficient A rho p z).2 := by
  classical
  let : CompactSpace sphereAtlasCore := isCompact_iff_compactSpace.mp sphereAtlasCore_compact
  let c : {p // p ∈ P} × sphereAtlasCore → CoefficientPoint BaseModel :=
    fun t ↦ intrinsicChartCoefficient A rho t.1.val t.2.val
  have hc : Continuous c := continuous_prod_of_discrete_left.mpr
    (fun p ↦ (intrinsic_coefficient_chart_smooth A hA hs hp rho hr p.val).continuous.comp continuous_subtype_val)
  obtain ⟨m,hm,hbound,hrbound⟩ := compact_contravariant_margin c hc
    (fun t alpha hn ↦ intrinsicChartCoefficient_positive A hs hp rho t.1.val
      (by rw [centeredSphereChart_target]; trivial) alpha hn)
    (fun t ↦ hrp ((extChartAt (𝓡 4) t.1.val).symm t.2.val))
  exact ⟨m,hm,fun p hp z hz ↦ ⟨hbound (⟨p,hp⟩,⟨z,hz⟩),hrbound (⟨p,hp⟩,⟨z,hz⟩)⟩⟩

lemma sphereCoefficientDistance_value_bound (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p))
    (p : Base) (hp : p ∈ P) (z : BaseModel) (hz : z ∈ sphereAtlasCore) :
    ‖intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z‖ ≤
      sphereCoefficientDistance P J A rho B sigma := by
  simpa only [sphereCoefficientDistance,norm_iteratedFDeriv_zero] using norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J
    (fun p z ↦ intrinsicChartCoefficient B sigma p z-intrinsicChartCoefficient A rho p z)
    (fun p hp ↦ (hB p hp).sub (hA p hp)) p hp 0 (Nat.zero_le _) z hz

theorem sphere_coefficient_relative_form_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta > 0, ∀ (B : IntrinsicTensor) (sigma : Base → ℝ),
      IntrinsicTensorSmooth B → (∀ x alpha beta, B x alpha beta = B x beta alpha) →
      (∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha) →
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ sigma →
      sphereCoefficientDistance P 0 A rho B sigma < eta →
      ∀ x : Base, (∀ alpha : SphereCotangent x,
        |B x alpha alpha-A x alpha alpha| ≤ eps*A x alpha alpha) ∧
        |sigma x-rho x| ≤ eps*rho x := by
  obtain ⟨m,hm,hmargin⟩ := sphere_finite_atlas_coercivity P A hA hs hp rho hr hrp
  refine ⟨eps*m,mul_pos heps hm,?_⟩
  intro B sigma hB hBs hBp hsig hdist x
  obtain ⟨p,hpP,z,hz,rfl⟩ := hcover x
  have hcmp := coefficient_relative_comparison (intrinsicChartCoefficient A rho p z)
    (intrinsicChartCoefficient B sigma p z) hm heps.le (hmargin p hpP z hz).1 (hmargin p hpP z hz).2
    ((sphereCoefficientDistance_value_bound P 0 A B rho sigma
      (fun p _ ↦ intrinsic_coefficient_chart_smooth A hA hs hp rho hr p)
      (fun p _ ↦ intrinsic_coefficient_chart_smooth B hB hBs hBp sigma hsig p) p hpP z hz).trans hdist.le)
  refine ⟨?_,hcmp.2⟩
  intro alpha
  let beta : BaseModel →L[ℝ] ℝ := alpha.comp
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm z)
  have hrep : sphereCoordinateCovector p z (baseCovectorCoordinates beta) = alpha := by
    symm
    apply sphereCoordinateCovector_unique p (by rw [centeredSphereChart_target]; trivial)
    intro w
    change beta (WithLp.toLp 2 w) = _
    exact baseCovectorCoordinates_apply beta _
  have h := hcmp.1 beta
  rw [intrinsicChartCoefficient_pair B sigma,intrinsicChartCoefficient_pair A rho,hrep] at h
  exact h

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
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_UniformSummableIncrements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Filter Set
open scoped Topology
noncomputable section
variable {X F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

theorem uniform_limit_of_summable_increments (f : ℕ → X → F) (S : Set X)
    (b : ℕ → ℝ) (hb : Summable b)
    (hstep : ∀ n x, x ∈ S → dist (f n x) (f (n+1) x) ≤ b n) :
    ∃ g : X → F, TendstoUniformlyOn f g atTop S ∧
      ∀ n x, x ∈ S → dist (f n x) (g x) ≤ ∑' j, b (n+j) := by
  classical
  have hex (x : S) : ∃ y : F, Tendsto (fun n ↦ f n x.val) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable b (fun n ↦ hstep n x.val x.property) hb)
  choose g hg using hex
  let G : X → F := fun x ↦ if hx : x ∈ S then g ⟨x,hx⟩ else 0
  have hpoint (x : X) (hx : x ∈ S) : Tendsto (fun n ↦ f n x) atTop (𝓝 (G x)) := by
    simpa only [G,dite_eq_left hx] using hg ⟨x,hx⟩
  have htail (n : ℕ) (x : X) (hx : x ∈ S) :
      dist (f n x) (G x) ≤ ∑' j, b (n+j) :=
    dist_le_tsum_of_dist_le_of_tendsto b (fun n ↦ hstep n x hx) hb (hpoint x hx) n
  refine ⟨G,?_,htail⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have ht : Tendsto (fun n ↦ ∑' j, b (n+j)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add b
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with n hn x hx
  rw [dist_comm]
  exact (htail n x hx).trans_lt hn

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_FiniteJetSummableTailLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Analysis

section

open Filter Set
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem finite_jet_summable_tail (f : ℕ → E → F) (g : E → F)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hg : ContDiff ℝ ∞ g)
    (Q : Set E) (hQ : Q ⊆ closure (interior Q))
    (hpoint : ∀ x ∈ interior Q, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (J : ℕ) (b : ℕ → ℝ) (hb : Summable b)
    (hstep : ∀ k, k ≤ J → ∀ n x, x ∈ Q →
      dist (iteratedFDeriv ℝ k (f n) x) (iteratedFDeriv ℝ k (f (n+1)) x) ≤ b n) :
    ∀ k, k ≤ J →
      TendstoUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (f n)) (iteratedFDeriv ℝ k g) atTop Q ∧
      ∀ n x, x ∈ Q → dist (iteratedFDeriv ℝ k (f n) x) (iteratedFDeriv ℝ k g x) ≤
        ∑' j, b (n+j) := by
  classical
  have hex (k : Fin (J+1)) := uniform_limit_of_summable_increments
    (fun n ↦ iteratedFDeriv ℝ k.val (f n)) Q b hb (hstep k.val (by omega))
  choose u hu htail using hex
  have hid (k : ℕ) (hk : k ≤ J) :
      EqOn (iteratedFDeriv ℝ k g) (u ⟨k,by omega⟩) (interior Q) := by
    induction k with
    | zero =>
      intro x hx
      exact tendsto_nhds_unique
        ((continuousMultilinearCurryFin0 ℝ E F).symm.continuous.tendsto (g x) |>.comp (hpoint x hx))
        ((hu ⟨0,by omega⟩).tendsto_at (interior_subset hx))
    | succ k ih =>
      intro x hx
      let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F
      have hd : HasFDerivAt (iteratedFDeriv ℝ k g) (C (u ⟨k+1,by omega⟩ x)) x := by
        apply hasFDerivAt_of_tendstoUniformlyOn isOpen_interior
          (C.isometry.uniformContinuous.comp_tendstoUniformlyOn
            ((hu ⟨k+1,by omega⟩).mono interior_subset))
          (f := fun n ↦ iteratedFDeriv ℝ k (f n))
        · intro n y hy
          exact ((hf n).differentiable_iteratedFDeriv
            (by exact_mod_cast (show (k:ℕ∞) < ⊤ from WithTop.coe_lt_top k)) y).hasFDerivAt
        · intro y hy
          rw [ih (by omega) hy]
          exact (hu ⟨k,by omega⟩).tendsto_at (interior_subset hy)
        · exact hx
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,hd.fderiv]
      exact C.symm_apply_apply _
  intro k hk
  have hc : ContinuousOn (u ⟨k,by omega⟩) Q := (hu ⟨k,by omega⟩).continuousOn
    (Filter.Frequently.of_forall (fun n ↦ ((hf n).continuous_iteratedFDeriv
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).continuousOn))
  have he : EqOn (iteratedFDeriv ℝ k g) (u ⟨k,by omega⟩) Q :=
    (hid k hk).of_subset_closure
      (hg.continuous_iteratedFDeriv (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).continuousOn
      hc interior_subset hQ
  refine ⟨(hu ⟨k,by omega⟩).congr_right he.symm,?_⟩
  intro n x hx
  rw [he hx]
  exact htail ⟨k,by omega⟩ n x hx

end

open Filter Set
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem smooth_limit_of_summable_jets (f : ℕ → E → F)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (S : Set E) (hS : IsOpen S)
    (b : ℕ → ℕ → ℝ) (hb : ∀ k, Summable (b k))
    (hstep : ∀ k n x, x ∈ S →
      dist (iteratedFDeriv ℝ k (f n) x) (iteratedFDeriv ℝ k (f (n+1)) x) ≤ b k n) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g S ∧
      ∀ k, TendstoUniformlyOn (fun n ↦ iteratedFDeriv ℝ k (f n))
        (iteratedFDeriv ℝ k g) atTop S := by
  classical
  have hex (k : ℕ) := uniform_limit_of_summable_increments
    (fun n ↦ iteratedFDeriv ℝ k (f n)) S (b k) (hb k) (hstep k)
  choose u hu htail using hex
  let curry (k : ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F
  have hc (k : ℕ) : ContinuousOn (u k) S :=
    (hu k).continuousOn (Filter.Frequently.of_forall (fun n ↦
      ((hf n).continuous_iteratedFDeriv (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).continuousOn))
  have hd (k : ℕ) (x : E) (hx : x ∈ S) :
      HasFDerivAt (u k) (curry k (u (k+1) x)) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hS
      ((curry k).isometry.uniformContinuous.comp_tendstoUniformlyOn (hu (k+1)))
      (f := fun n ↦ iteratedFDeriv ℝ k (f n))
    · intro n y hy
      exact ((hf n).differentiable_iteratedFDeriv (by exact_mod_cast
        (show (k:ℕ∞) < ⊤ from WithTop.coe_lt_top k)) y).hasFDerivAt
    · intro y hy
      exact (hu k).tendsto_at hy
    · exact hx
  have hsmooth (m : ℕ) : ∀ k, ContDiffOn ℝ m (u k) S := by
    induction m with
    | zero => intro k; exact contDiffOn_zero.mpr (hc k)
    | succ m ih =>
      intro k
      rw [show ((m+1:ℕ):ℕ∞ω) = (m:ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hS]
      refine ⟨fun x hx ↦ (hd k x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
      apply ((curry k).contDiff.comp_contDiffOn (ih (k+1))).congr
      intro x hx
      exact (hd k x hx).fderiv
  let ev := (continuousMultilinearCurryFin0 ℝ E F)
  let g : E → F := fun x ↦ ev (u 0 x)
  have hg : ContDiffOn ℝ ∞ g S :=
    ev.contDiff.comp_contDiffOn (contDiffOn_infty.mpr (fun m ↦ hsmooth m 0))
  have hid (k : ℕ) : EqOn (iteratedFDeriv ℝ k g) (u k) S := by
    induction k with
    | zero =>
      intro x hx
      change ev.symm (ev (u 0 x)) = u 0 x
      exact ev.symm_apply_apply _
    | succ k ih =>
      intro x hx
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
      have he : iteratedFDeriv ℝ k g =ᶠ[𝓝 x] u k :=
        Filter.mem_of_superset (hS.mem_nhds hx) (fun y hy ↦ ih hy)
      rw [he.fderiv_eq,(hd k x hx).fderiv]
      exact (curry k).symm_apply_apply _
  refine ⟨g,hg,?_⟩
  intro k
  exact (hu k).congr_right (fun x hx ↦ (hid k hx).symm)

end Yau.Analysis

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereSummableChartLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sphere_coefficient_jet_increment_bound (P : Finset Base) (J : ℕ)
    (a b : SphereEnergyData)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a.density)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (p : Base) (hp : p ∈ P) (k : ℕ) (hk : k ≤ J)
    (z : BaseModel) (hz : z ∈ sphereAtlasCore) :
    dist (iteratedFDeriv ℝ k (intrinsicChartCoefficient a.tensor a.density p) z)
      (iteratedFDeriv ℝ k (intrinsicChartCoefficient b.tensor b.density p) z) ≤
      sphereCoefficientDistance P J a.tensor a.density b.tensor b.density := by
  have hca := intrinsic_coefficient_chart_smooth a.tensor a.smooth a.symm a.pos a.density ha
  have hcb := intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb
  have h := norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J
    (fun p z ↦ intrinsicChartCoefficient b.tensor b.density p z-
      intrinsicChartCoefficient a.tensor a.density p z)
    (fun p _ ↦ (hcb p).sub (hca p)) p hp k hk z hz
  rw [fun_iteratedFDeriv_sub_apply
    ((hcb p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((hca p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt] at h
  simpa only [sphereCoefficientDistance,dist_eq_norm, norm_sub_rev] using h

theorem sphere_summable_chart_limit (P : Finset Base) (d : ℕ → SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density)
    (hseq : ∀ J, Summable (fun n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density))
    (p : Base) (hp : p ∈ P) :
    ∃ c : BaseModel → CoefficientPoint BaseModel,
      ContDiffOn ℝ ∞ c (interior sphereAtlasCore) ∧
      ∀ z ∈ interior sphereAtlasCore,
        Tendsto (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p z)
          atTop (𝓝 (c z)) := by
  obtain ⟨c,hc,ht⟩ := smooth_limit_of_summable_jets
    (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p)
    (fun n ↦ intrinsic_coefficient_chart_smooth (d n).tensor (d n).smooth
      (d n).symm (d n).pos (d n).density (hd n) p)
    (interior sphereAtlasCore) isOpen_interior
    (fun J n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density) hseq
    (fun k n z hz ↦ sphere_coefficient_jet_increment_bound P k (d n) (d (n+1))
      (hd n) (hd (n+1)) p hp k le_rfl z (interior_subset hz))
  refine ⟨c,hc,?_⟩
  intro z hz
  have h := (continuousMultilinearCurryFin0 ℝ BaseModel (CoefficientPoint BaseModel)).continuous.tendsto
    (iteratedFDeriv ℝ 0 c z) |>.comp ((ht 0).tendsto_at hz)
  exact h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientLimitTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Set Filter Metric
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sphereAtlasCore_subset_closure_interior :
    sphereAtlasCore ⊆ closure (interior sphereAtlasCore) := by
  rintro z ⟨y,hy,rfl⟩
  have hy' : y ∈ closure (ball (0 : Yau.Jets.Coord) 1) := by
    rw [closure_ball _ one_ne_zero]
    exact hy
  apply closure_mono (s := seedCoordEquiv '' ball (0 : Yau.Jets.Coord) 1) ?_
    (mem_closure_image seedCoordEquiv.continuous.continuousAt hy')
  exact (seedCoordEquiv.isOpenMap _ isOpen_ball).subset_interior_iff.mpr
    (image_mono ball_subset_closedBall)

theorem sphere_coefficient_limit_tail (P : Finset Base) (J : ℕ)
    (d : ℕ → SphereEnergyData) (a : SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a.density)
    (hpoint : ∀ p ∈ P, ∀ z ∈ interior sphereAtlasCore,
      Tendsto (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p z)
        atTop (𝓝 (intrinsicChartCoefficient a.tensor a.density p z)))
    (hseq : Summable (fun n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density)) :
    Tendsto (fun n ↦ sphereCoefficientDistance P J (d n).tensor (d n).density a.tensor a.density)
      atTop (𝓝 0) ∧
    ∀ n, sphereCoefficientDistance P J (d n).tensor (d n).density a.tensor a.density ≤
      ∑' j, sphereCoefficientDistance P J (d (n+j)).tensor (d (n+j)).density
        (d (n+j+1)).tensor (d (n+j+1)).density := by
  let b : ℕ → ℝ := fun n ↦ sphereCoefficientDistance P J
    (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density
  have hds (n : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d n).tensor (d n).smooth (d n).symm (d n).pos (d n).density (hd n) p
  have has (p : Base) := intrinsic_coefficient_chart_smooth
    a.tensor a.smooth a.symm a.pos a.density ha p
  have hnonneg (n : ℕ) : 0 ≤ b n := sphereCoefficientDistance_nonneg P J
    (d n).tensor (d (n+1)).tensor (d n).density (d (n+1)).density
    (fun p _ ↦ hds n p) (fun p _ ↦ hds (n+1) p)
  have hjet (p : Base) (hp : p ∈ P) := finite_jet_summable_tail
    (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p)
    (intrinsicChartCoefficient a.tensor a.density p) (fun n ↦ hds n p) (has p)
    sphereAtlasCore sphereAtlasCore_subset_closure_interior (hpoint p hp) J b hseq
    (fun k hk n z hz ↦ sphere_coefficient_jet_increment_bound P J (d n) (d (n+1))
      (hd n) (hd (n+1)) p hp k hk z hz)
  have htail (n : ℕ) : sphereCoefficientDistance P J (d n).tensor (d n).density a.tensor a.density ≤
      ∑' j, b (n+j) := by
    apply finiteChartDerivativeSize_le _ _ _ _ (tsum_nonneg (fun j ↦ hnonneg (n+j)))
    intro p hp k hk z hz
    rw [fun_iteratedFDeriv_sub_apply
      ((has p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      ((hds n p).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
    simpa only [dist_eq_norm,norm_sub_rev] using (hjet p hp k hk).2 n z hz
  refine ⟨?_,htail⟩
  apply squeeze_zero (fun n ↦ sphereCoefficientDistance_nonneg P J
    (d n).tensor a.tensor (d n).density a.density (fun p _ ↦ hds n p) (fun p _ ↦ has p)) htail
  simpa only [Nat.add_comm] using tendsto_sum_nat_add b

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereFiniteCoefficientConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_finite_coefficient_constraints {ι : Type*}
    (s : Finset ι) (P : ι → Finset Base) (J : ι → ℕ) (eps : ι → ℝ)
    (heps : ∀ i ∈ s, 0 < eps i) :
    ∃ (Q : Finset Base) (m : ℕ) (eta : ℝ), 0 < eta ∧
      ∀ (d b : SphereEnergyData),
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
        sphereCoefficientDistance Q m d.tensor d.density b.tensor b.density < eta →
        ∀ i ∈ s, sphereCoefficientDistance (P i) (J i) d.tensor d.density b.tensor b.density < eps i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,0,1,by norm_num,by simp⟩
  | @insert i s his ih =>
    obtain ⟨Q,m,eta,heta,H⟩ := ih (fun j hj ↦ heps j (Finset.mem_insert_of_mem hj))
    refine ⟨P i ∪ Q,max (J i) m,min (eps i) eta,
      lt_min (heps i (Finset.mem_insert_self _ _)) heta,?_⟩
    intro d b hd hb hdist j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (sphereCoefficientDistance_mono_order (P j) d b hd hb (J j) (max (J j) m) (le_max_left _ _)).trans_lt
        ((sphereCoefficientDistance_mono_atlas (P j) (P j ∪ Q) Finset.subset_union_left d b hd hb _).trans_lt
          (hdist.trans_le (min_le_left _ _)))
    · apply H d b hd hb ?_ j hj
      exact (sphereCoefficientDistance_mono_order Q d b hd hb m (max (J i) m) (le_max_right _ _)).trans_lt
        ((sphereCoefficientDistance_mono_atlas Q (P i ∪ Q) Finset.subset_union_right d b hd hb _).trans_lt
          (hdist.trans_le (min_le_right _ _)))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedFrequencyDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Filter Manifold
open scoped Topology ContDiff ENNReal
noncomputable section

lemma seed_window_eigenvalues_tendsto (N : ℕ → ℕ) (mu : ℕ → ℝ)
    (hN : ∀ k, k+1 ≤ N k) (hmu : ∀ k, seedEigenvalue (N k)/2 ≤ mu k) :
    Tendsto mu atTop atTop := by
  apply tendsto_atTop_mono (fun k ↦ ?_) (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ ↦ (k:ℝ)) atTop atTop)
  have hk : (k:ℝ)+1 ≤ N k := by exact_mod_cast hN k
  have hn : (0:ℝ) ≤ N k := Nat.cast_nonneg _
  have hh := hmu k
  unfold seedEigenvalue at hh
  nlinarith [sq_nonneg (N k:ℝ)]

theorem mainTarget_of_seed_windows (g : SmoothMetric) (N : ℕ → ℕ)
    (mu : ℕ → ℝ) (u : ℕ → Manifold5 → ℝ)
    (hN : ∀ k, k+1 ≤ N k)
    (hmu : ∀ k, 0 < mu k) (hwindow : ∀ k, seedEigenvalue (N k)/2 ≤ mu k)
    (hu0 : ∀ k, u k ≠ 0) (hu : ∀ k, ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (u k))
    (he : ∀ k x, -chartLaplacian g (extChartAt modelWithCorners x) (u k) (extChartAt modelWithCorners x x) =
      mu k*u k x)
    (hratio : ∀ k : ℕ, ENNReal.ofReal ((k:ℝ)+1) < nodalMeasure g (u k)/ENNReal.ofReal (Real.sqrt (mu k))) :
    MainTarget := by
  refine ⟨g,mu,u,hmu,hu0,hu,he,seed_window_eigenvalues_tendsto N mu hN hwindow,?_⟩
  apply tendsto_nhds_top_mono' ?_ (fun k ↦ (hratio k).le)
  apply ENNReal.tendsto_ofReal_atTop.comp
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_IterationGeometricTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open Filter
open scoped Topology
noncomputable section

theorem hasSum_scaled_geometric_shift (r : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ ↦ r*(1/2:ℝ)^(n+m)) (r*(1/2:ℝ)^m*2) := by
  simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using
    hasSum_geometric_two.mul_left (r*(1/2:ℝ)^m)

theorem tsum_scaled_geometric_two (r : ℝ) :
    (∑' n : ℕ, r*(1/2:ℝ)^(n+2)) = r/2 := by
  convert (hasSum_scaled_geometric_shift r 2).tsum_eq using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem tsum_scaled_geometric_three (r : ℝ) :
    (∑' n : ℕ, r*(1/2:ℝ)^(n+3)) = r/4 := by
  convert (hasSum_scaled_geometric_shift r 3).tsum_eq using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereSummableSmoothPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.summablePairTangentNormedGroup
attribute [local instance] OAI.Yau.Target.summablePairTangentNormedSpace
attribute [local instance] OAI.Yau.Target.summablePairCotangentNormedGroup
attribute [local instance] OAI.Yau.Target.summablePairCotangentNormedSpace
lemma intrinsicChartCoefficient_tendsto_of_pairings (d : ℕ → SphereEnergyData)
    (A : IntrinsicTensor) (rho : Base → ℝ)
    (hA : ∀ x alpha beta, Tendsto (fun n ↦ (d n).tensor x alpha beta)
      atTop (𝓝 (A x alpha beta)))
    (hr : ∀ x, Tendsto (fun n ↦ (d n).density x) atTop (𝓝 (rho x)))
    (p : Base) (z : BaseModel) :
    Tendsto (fun n ↦ intrinsicChartCoefficient (d n).tensor (d n).density p z)
      atTop (𝓝 (intrinsicChartCoefficient A rho p z)) := by
  apply Tendsto.prodMk_nhds _ (hr _)
  unfold matrixContravariant
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (hA _ _ _).smul tendsto_const_nhds

theorem sphere_summable_smooth_pair (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z=x)
    (d : ℕ → SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density)
    (hseq : ∀ J, Summable (fun n ↦ sphereCoefficientDistance P J
      (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density)) :
    ∃ (A : IntrinsicTensor) (rho : Base → ℝ), IntrinsicTensorSmooth A ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho ∧
      (∀ x alpha beta, Tendsto (fun n ↦ (d n).tensor x alpha beta)
        atTop (𝓝 (A x alpha beta))) ∧
      (∀ x, Tendsto (fun n ↦ (d n).density x) atTop (𝓝 (rho x))) := by
  classical
  choose c hc ht using (fun p : P ↦ sphere_summable_chart_limit P d hd hseq p.val p.property)
  have hentry (i j : Fin 5) : ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ∀ x, Tendsto (fun n ↦ intrinsicAmbientMatrix (d n).tensor x i j) atTop (𝓝 (v x)) := by
    apply sphere_local_limit_gluing P hcover
      (fun n x ↦ intrinsicAmbientMatrix (d n).tensor x i j)
    intro p hp
    let q : P := ⟨p,hp⟩
    refine ⟨coefficientAmbientEntry p (c q) i j,
      coefficientAmbientEntry_smoothOn p (c q) (hc q) i j,?_⟩
    intro z hz
    have h := ((sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ i) z).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ BaseModel
        (sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ j) z)).continuous.tendsto _).comp
        (continuous_fst.tendsto _ |>.comp (ht q z hz)))
    have hh := h.add (tendsto_const_nhds (x :=
      (((extChartAt (𝓡 4) p).symm z : AmbientBase) i) *
        (((extChartAt (𝓡 4) p).symm z : AmbientBase) j)))
    change Tendsto (fun n ↦ coefficientAmbientEntry p
      (intrinsicChartCoefficient (d n).tensor (d n).density p) i j z) atTop
      (𝓝 (coefficientAmbientEntry p (c q) i j z)) at hh
    simpa only [coefficientAmbientEntry_intrinsic] using hh
  choose B hB hBt using hentry
  obtain ⟨rho,hr,hrt⟩ := sphere_local_limit_gluing P hcover (fun n ↦ (d n).density) (by
    intro p hp
    refine ⟨fun z ↦ (c ⟨p,hp⟩ z).2,(hc ⟨p,hp⟩).snd,?_⟩
    intro z hz
    exact continuous_snd.tendsto _ |>.comp (ht ⟨p,hp⟩ z hz))
  let A : IntrinsicTensor := fun x ↦ bilinearPullback
    (ambientMatrixForm (fun i j ↦ B i j x)) (sphereCotangentRepresentative x)
  have hAs : IntrinsicTensorSmooth A := smooth_bilinear_pullback
    (fun x ↦ ambientMatrixForm (fun i j ↦ B i j x)) sphereCotangentRepresentative
    (ambientMatrixForm_smooth _ hB) sphereCotangentRepresentative_smooth
  refine ⟨A,rho,hAs,hr,?_,hrt⟩
  intro x alpha beta
  have h (n : ℕ) : (d n).tensor x alpha beta =
      ambientMatrixForm (intrinsicAmbientMatrix (d n).tensor x)
        (sphereCotangentRepresentative x alpha) (sphereCotangentRepresentative x beta) := by
    rw [intrinsicAmbientMatrix_pairing,sphereCotangentRepresentative_restriction,
      sphereCotangentRepresentative_restriction,sphereCotangentRepresentative_orthogonal,
      zero_mul,add_zero]
  simp only [h,A,bilinearPullback_apply,ambientMatrixForm_apply]
  erw [ambientMatrixForm_apply]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (tendsto_const_nhds.mul (hBt i j x)).mul tendsto_const_nhds

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereCoefficientSummablePositiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphereCoefficientDistance_le_sum_range (P : Finset Base) (J : ℕ)
    (d : ℕ → SphereEnergyData)
    (hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density) (n : ℕ) :
    sphereCoefficientDistance P J (d 0).tensor (d 0).density (d n).tensor (d n).density ≤
      ∑ k ∈ Finset.range n, sphereCoefficientDistance P J
        (d k).tensor (d k).density (d (k+1)).tensor (d (k+1)).density := by
  have hs (k : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d k).tensor (d k).smooth (d k).symm (d k).pos (d k).density (hd k) p
  induction n with
  | zero => simp only [sphereCoefficientDistance_self,Finset.range_zero,Finset.sum_empty,le_refl]
  | succ n ih =>
    exact (sphereCoefficientDistance_triangle P J (d 0).tensor (d n).tensor (d (n+1)).tensor
      (d 0).density (d n).density (d (n+1)).density (fun p _ ↦ hs 0 p)
      (fun p _ ↦ hs n p) (fun p _ ↦ hs (n+1) p)).trans
      (by
        simpa only [Finset.sum_range_succ,add_comm] using add_le_add_right ih
          (sphereCoefficientDistance P J (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density))

theorem sphere_coefficient_summable_positive_limit (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z=x)
    (a : SphereEnergyData) (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a.density) :
    ∃ eta > 0, ∀ (d : ℕ → SphereEnergyData),
      (∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d k).density) → d 0=a →
      (∀ J : ℕ, Summable (fun k ↦ sphereCoefficientDistance P J (d k).tensor (d k).density
        (d (k+1)).tensor (d (k+1)).density)) →
      (∑' k, sphereCoefficientDistance P 0 (d k).tensor (d k).density
        (d (k+1)).tensor (d (k+1)).density) < eta →
      ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
        ∀ (Q : Finset Base) (J : ℕ),
          Summable (fun k ↦ sphereCoefficientDistance Q J (d k).tensor (d k).density
            (d (k+1)).tensor (d (k+1)).density) →
          Tendsto (fun k ↦ sphereCoefficientDistance Q J (d k).tensor (d k).density b.tensor b.density)
            atTop (𝓝 0) ∧
          ∀ k, sphereCoefficientDistance Q J (d k).tensor (d k).density b.tensor b.density ≤
            ∑' j, sphereCoefficientDistance Q J (d (k+j)).tensor (d (k+j)).density
              (d (k+j+1)).tensor (d (k+j+1)).density := by
  have hcover' : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z=x := by
    intro x
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨p,hp,z,interior_subset hz,he⟩
  obtain ⟨eta,heta,H⟩ := sphere_coefficient_relative_form_comparison P hcover'
    a.tensor a.smooth a.symm a.pos a.density ha a.positive (1/2) (by norm_num)
  refine ⟨eta,heta,?_⟩
  intro d hd hzero hseq hsmall
  obtain ⟨A,rho,hAs,hr,hAt,hrt⟩ := sphere_summable_smooth_pair P hcover d hd hseq
  have hds (n : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d n).tensor (d n).smooth (d n).symm (d n).pos (d n).density (hd n) p
  have hdist (n : ℕ) :
      sphereCoefficientDistance P 0 a.tensor a.density (d n).tensor (d n).density < eta := by
    have h := sphereCoefficientDistance_le_sum_range P 0 d hd n
    rw [hzero] at h
    apply h.trans_lt
    apply lt_of_le_of_lt _ hsmall
    exact (hseq 0).sum_le_tsum (Finset.range n) (fun k _ ↦ sphereCoefficientDistance_nonneg P 0
      (d k).tensor (d (k+1)).tensor (d k).density (d (k+1)).density
      (fun p _ ↦ hds k p) (fun p _ ↦ hds (k+1) p))
  have hcmp (n : ℕ) (x : Base) := H (d n).tensor (d n).density (d n).smooth
    (d n).symm (d n).pos (hd n) (hdist n) x
  have hsym : ∀ x alpha beta, A x alpha beta = A x beta alpha := by
    intro x alpha beta
    apply tendsto_nhds_unique (hAt x alpha beta)
    simpa only [(d _).symm] using hAt x beta alpha
  have hpos : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha := by
    intro x alpha hn
    have hle : a.tensor x alpha alpha/2 ≤ A x alpha alpha :=
      ge_of_tendsto (hAt x alpha alpha) (Filter.Eventually.of_forall (fun n ↦ by
        have h := (abs_le.mp ((hcmp n x).1 alpha)).1
        linarith))
    exact lt_of_lt_of_le (half_pos (a.pos x alpha hn)) hle
  have hrpos (x : Base) : 0 < rho x := by
    have hle : a.density x/2 ≤ rho x :=
      ge_of_tendsto (hrt x) (Filter.Eventually.of_forall (fun n ↦ by
        have h := (abs_le.mp (hcmp n x).2).1
        linarith))
    exact lt_of_lt_of_le (half_pos (a.positive x)) hle
  let b : SphereEnergyData := ⟨A,hAs,hsym,hpos,rho,hr.continuous,hrpos⟩
  refine ⟨b,hr,?_⟩
  intro Q J hsum
  exact sphere_coefficient_limit_tail Q J d b hd hr
    (fun p _ z _ ↦ intrinsicChartCoefficient_tendsto_of_pairings d A rho hAt hrt p z) hsum

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereIterationSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

theorem sphere_coefficient_diagonal_summable (P : Finset Base) (d : ℕ → SphereEnergyData)
    (hd : ∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d k).density)
    (hstep : ∀ k, sphereCoefficientDistance P (k+1) (d k).tensor (d k).density
      (d (k+1)).tensor (d (k+1)).density < (1/2:ℝ)^(k+1)) :
    ∀ J : ℕ, Summable (fun k ↦ sphereCoefficientDistance P J (d k).tensor (d k).density
      (d (k+1)).tensor (d (k+1)).density) := by
  intro J
  have hgeom : Summable (fun k : ℕ ↦ (1/2:ℝ)^(k+1)) :=
    summable_geometric_two.comp_injective (fun _ _ h ↦ Nat.succ.inj h)
  apply Summable.of_norm_bounded_eventually hgeom
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop J] with k hk
  have hnonneg := sphereCoefficientDistance_nonneg P J (d k).tensor (d (k+1)).tensor
    (d k).density (d (k+1)).density
    (fun p _ ↦ intrinsic_coefficient_chart_smooth (d k).tensor (d k).smooth (d k).symm (d k).pos (d k).density (hd k) p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth (d (k+1)).tensor (d (k+1)).smooth (d (k+1)).symm (d (k+1)).pos
      (d (k+1)).density (hd (k+1)) p)
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  exact (sphereCoefficientDistance_mono_order P (d k) (d (k+1)) (hd k) (hd (k+1)) J (k+1) (by omega)).trans (hstep k).le

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_FiniteHistorySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau

theorem exists_sequence_of_finite_history {X : ℕ → Type*} (x₀ : X 0)
    (R : (n : ℕ) → ((i : Fin (n+1)) → X i.val) → X (n+1) → Prop)
    (H : ∀ n v, ∃ w, R n v w) :
    ∃ x : (n : ℕ) → X n, x 0=x₀ ∧ ∀ n, R n (fun i ↦ x i.val) (x (n+1)) := by
  classical
  choose next hnext using H
  let rows : (n : ℕ) → (i : Fin (n+1)) → X i.val :=
    Nat.rec (Fin.snoc (fun i : Fin 0 ↦ Fin.elim0 i) x₀)
      (fun n v ↦ Fin.snoc v (next n v))
  let x : (n : ℕ) → X n := fun n ↦ rows n (Fin.last n)
  have hprefix : ∀ n (i : Fin (n+1)), rows n i=x i.val := by
    intro n
    induction n with
    | zero => intro i; have hi : i=Fin.last 0 := Fin.ext (by omega); subst i; rfl
    | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rfl
      · change (Fin.snoc (α := fun i : Fin (n+2) ↦ X i.val) (rows n) (next n (rows n))) j.castSucc=x j.val
        rw [Fin.snoc_castSucc]
        exact ih j
  refine ⟨x,?_,?_⟩
  · change Fin.snoc (α := fun i : Fin 1 ↦ X i.val) (fun i : Fin 0 ↦ Fin.elim0 i) x₀ (Fin.last 0)=x₀
    rw [Fin.snoc_last]
  · intro n
    have hp : rows n=(fun i : Fin (n+1) ↦ x i.val) := funext (hprefix n)
    have he : x (n+1)=next n (rows n) := by
      change Fin.snoc (α := fun i : Fin (n+2) ↦ X i.val) (rows n) (next n (rows n)) (Fin.last (n+1))=next n (rows n)
      rw [Fin.snoc_last]
    rw [he,← hp]
    exact hnext n (rows n)

end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereIterationInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal
noncomputable section

theorem sphere_iteration_interface :
    ∃ r delta : ℝ, 0 < r ∧ 0 < delta ∧
      (∃ d : SphereComparisonPair r delta, d.energy=roundSphereEnergyData ∧ d.support=∅) ∧
      SphereStageExtension r delta := by
  obtain ⟨r,a,delta,hr,ha,hdelta,hcube,hbranch,H⟩ := intrinsic_one_step
  refine ⟨r,delta,hr,hdelta,?_,?_⟩
  · exact ⟨⟨roundSphereEnergyData,roundSphereEnergyData_density_smooth,
      roundSphereEnergyData_comparison r hdelta,∅,isCompact_empty,empty_subset _,
      roundSphereEnergyData_exterior.1,roundSphereEnergyData_exterior.2⟩,rfl,rfl⟩
  · intro d k P J eps heps n₀
    obtain ⟨n,hn,hn0,b,hb,hclose,hcomp,K,hK,hsub,hKP,hA,hrho,Q,eta,heta,Heta⟩ :=
      H d.energy d.density_smooth d.comparison d.support d.support_compact d.support_patch
        d.exterior_tensor d.exterior_density ((k:ℝ)+1) (by positivity) P J eps heps n₀
    exact ⟨⟨⟨b,hb,hcomp,K,hK,hKP,hA,hrho⟩,n,hn0,Q,eta,heta,Heta⟩,hn,hsub,hclose⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereSummableIterationSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace ENNReal
noncomputable section

theorem sphere_summable_iteration_sequence (P₀ : Finset Base) (budget : ℝ) (hbudget : 0 < budget) :
    ∃ r delta : ℝ, 0 < r ∧ 0 < delta ∧
      ∃ s : (k : ℕ) → SphereNodalStage r delta k,
        sphereCoefficientDistance P₀ 0 roundSphereEnergyData.tensor roundSphereEnergyData.density
          (s 0).energy.tensor (s 0).energy.density < budget/4 ∧
        (∀ k, k+1 ≤ (s k).frequency) ∧
        (∀ k, 2*(s k).frequency+1 ≤ (s (k+1)).frequency) ∧
        (∀ k, (s k).support ⊆ (s (k+1)).support) ∧
        (∀ k, sphereCoefficientDistance P₀ (k+1) (s k).energy.tensor (s k).energy.density
          (s (k+1)).energy.tensor (s (k+1)).energy.density < (1/2:ℝ)^(k+1)) ∧
        (∀ k, sphereCoefficientDistance P₀ 0 (s k).energy.tensor (s k).energy.density
          (s (k+1)).energy.tensor (s (k+1)).energy.density < budget*(1/2:ℝ)^(k+3)) ∧
        (∀ k i, i ≤ k → sphereCoefficientDistance (s i).charts 8 (s k).energy.tensor (s k).energy.density
          (s (k+1)).energy.tensor (s (k+1)).energy.density < (s i).radius*(1/2:ℝ)^(k-i+2)) := by
  classical
  obtain ⟨r,delta,hr,hdelta,⟨d₀,hd₀,hsupp₀⟩,H⟩ := sphere_iteration_interface
  obtain ⟨s₀,hs₀,hsupp,hfirst⟩ := H d₀ 0 P₀ 0 (budget/4) (by positivity) 1
  let R : (k : ℕ) → ((i : Fin (k+1)) → SphereNodalStage r delta i.val) →
      SphereNodalStage r delta (k+1) → Prop := fun k v w ↦
    let d := v (Fin.last k)
    2*d.frequency+1 ≤ w.frequency ∧ d.support ⊆ w.support ∧
    sphereCoefficientDistance P₀ (k+1) d.energy.tensor d.energy.density w.energy.tensor w.energy.density < (1/2:ℝ)^(k+1) ∧
    sphereCoefficientDistance P₀ 0 d.energy.tensor d.energy.density w.energy.tensor w.energy.density < budget*(1/2:ℝ)^(k+3) ∧
    ∀ i : Fin (k+1), sphereCoefficientDistance (v i).charts 8 d.energy.tensor d.energy.density w.energy.tensor w.energy.density <
      (v i).radius*(1/2:ℝ)^(k-i.val+2)
  have Hnext : ∀ k v, ∃ w, R k v w := by
    intro k v
    let d := v (Fin.last k)
    obtain ⟨Q,m,eta,heta,Hsmall⟩ := sphere_finite_coefficient_constraints
      (Finset.univ : Finset (Fin (k+1))) (fun i ↦ (v i).charts) (fun _ ↦ 8)
      (fun i ↦ (v i).radius*(1/2:ℝ)^(k-i.val+2))
      (fun i _ ↦ mul_pos (v i).radius_pos (by positivity))
    let eps : ℝ := min eta (min ((1/2:ℝ)^(k+1)) (budget*(1/2:ℝ)^(k+3)))
    have heps : 0 < eps := by dsimp [eps] <;> positivity
    obtain ⟨w,hfreq,hsupport,hdist⟩ := H d.toSphereComparisonPair (k+1) (P₀ ∪ Q) (max (k+1) m)
      eps heps (2*d.frequency+1)
    have hdistP := (sphereCoefficientDistance_mono_atlas P₀ (P₀ ∪ Q) Finset.subset_union_left
      d.energy w.energy d.density_smooth w.density_smooth (max (k+1) m)).trans_lt hdist
    have hdistOrder := (sphereCoefficientDistance_mono_order P₀ d.energy w.energy d.density_smooth w.density_smooth
      (k+1) (max (k+1) m) (le_max_left _ _)).trans_lt hdistP
    refine ⟨w,hfreq,hsupport,?_,?_,?_⟩
    · exact hdistOrder.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    · exact ((sphereCoefficientDistance_mono_order P₀ d.energy w.energy d.density_smooth w.density_smooth
        0 (k+1) (Nat.zero_le _)).trans_lt hdistOrder).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
    · intro i
      apply Hsmall d.energy w.energy d.density_smooth w.density_smooth ?_ i (Finset.mem_univ i)
      exact (sphereCoefficientDistance_mono_order Q d.energy w.energy d.density_smooth w.density_smooth
        m (max (k+1) m) (le_max_right _ _)).trans_lt
        ((sphereCoefficientDistance_mono_atlas Q (P₀ ∪ Q) Finset.subset_union_right
          d.energy w.energy d.density_smooth w.density_smooth _).trans_lt (hdist.trans_le (min_le_left _ _)))
  obtain ⟨s,hs0,hs⟩ := Yau.exists_sequence_of_finite_history s₀ R Hnext
  have hprops (k : ℕ) := hs k
  change ∀ k, R k (fun i ↦ s i.val) (s (k+1)) at hs
  have hfreq (k : ℕ) : 2*(s k).frequency+1 ≤ (s (k+1)).frequency := (hs k).1
  refine ⟨r,delta,hr,hdelta,s,?_,?_,hfreq,fun k ↦ (hs k).2.1,
    fun k ↦ (hs k).2.2.1,fun k ↦ (hs k).2.2.2.1,?_⟩
  · rw [hs0,← hd₀]
    exact hfirst
  · intro k
    induction k with
    | zero => simpa only [hs0] using hs₀
    | succ k ih => have h := hfreq k; omega
  · intro k i hi
    exact (hs k).2.2.2.2 ⟨i,Nat.lt_succ_of_le hi⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SphereIterationPositiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Filter
open scoped ContDiff Topology
noncomputable section

theorem sphere_iteration_positive_limit :
    ∃ (r delta : ℝ) (s : (k : ℕ) → SphereNodalStage r delta k),
      (∀ k, k+1 ≤ (s k).frequency) ∧
      ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
        ∀ k, sphereCoefficientDistance (s k).charts 8
          (s k).energy.tensor (s k).energy.density b.tensor b.density < (s k).radius := by
  obtain ⟨P,hP⟩ := finite_sphere_coefficient_atlas
  obtain ⟨eta,heta,Hlimit⟩ := sphere_coefficient_summable_positive_limit P hP
    roundSphereEnergyData roundSphereEnergyData_density_smooth
  obtain ⟨r,delta,hr,hdelta,s,hfirst,hfreq,hgap,hsupp,hdiag,hzero,hpast⟩ :=
    sphere_summable_iteration_sequence P eta heta
  let d : ℕ → SphereEnergyData := fun n ↦ Nat.casesOn n roundSphereEnergyData (fun k ↦ (s k).energy)
  have hd : ∀ n, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d n).density := by
    rintro (_|n)
    · exact roundSphereEnergyData_density_smooth
    · exact (s n).density_smooth
  have hds (n : ℕ) (p : Base) := intrinsic_coefficient_chart_smooth
    (d n).tensor (d n).smooth (d n).symm (d n).pos (d n).density (hd n) p
  let D (Q : Finset Base) (J n : ℕ) : ℝ := sphereCoefficientDistance Q J
    (d n).tensor (d n).density (d (n+1)).tensor (d (n+1)).density
  have hnonneg (Q : Finset Base) (J n : ℕ) : 0 ≤ D Q J n :=
    sphereCoefficientDistance_nonneg Q J (d n).tensor (d (n+1)).tensor
      (d n).density (d (n+1)).density (fun p _ ↦ hds n p) (fun p _ ↦ hds (n+1) p)
  have hsum (J : ℕ) : Summable (D P J) := by
    apply (summable_nat_add_iff 1).mp
    exact sphere_coefficient_diagonal_summable P (fun k ↦ (s k).energy)
      (fun k ↦ (s k).density_smooth) hdiag J
  have hzero_le (n : ℕ) : D P 0 (n+1) ≤ eta*(1/2:ℝ)^(n+3) := (hzero n).le
  have htotal : (∑' n, D P 0 n) < eta := by
    have ht : (∑' n, D P 0 (n+1)) ≤ eta/4 := by
      rw [← tsum_scaled_geometric_three eta]
      exact ((summable_nat_add_iff 1).mpr (hsum 0)).tsum_le_tsum hzero_le
        (hasSum_scaled_geometric_shift eta 3).summable
    rw [(hsum 0).tsum_eq_zero_add]
    have hf : D P 0 0 < eta/4 := hfirst
    linarith
  obtain ⟨b,hb,Htail⟩ := Hlimit d hd rfl hsum htotal
  refine ⟨r,delta,s,hfreq,b,hb,?_⟩
  intro i
  have hpast_le (j : ℕ) : D (s i).charts 8 (j+(i+1)) ≤ (s i).radius*(1/2:ℝ)^(j+2) := by
    have h := hpast (i+j) i (Nat.le_add_right i j)
    simpa only [D,d,show j+(i+1) = (i+j)+1 by omega,Nat.casesOn,
      Nat.add_sub_cancel_left] using h.le
  have hsumtail : Summable (fun j ↦ D (s i).charts 8 (j+(i+1))) :=
    Summable.of_nonneg_of_le (fun j ↦ hnonneg _ _ _) hpast_le
      (hasSum_scaled_geometric_shift (s i).radius 2).summable
  have hsumall : Summable (D (s i).charts 8) := (summable_nat_add_iff (i+1)).mp hsumtail
  have ht := (Htail (s i).charts 8 hsumall).2 (i+1)
  have htsum : (∑' j, D (s i).charts 8 ((i+1)+j)) ≤ (s i).radius/2 := by
    rw [← tsum_scaled_geometric_two (s i).radius]
    have hs' : Summable (fun j ↦ D (s i).charts 8 ((i+1)+j)) := by
      simpa only [Nat.add_comm] using hsumtail
    exact hs'.tsum_le_tsum
      (fun j ↦ by simpa only [Nat.add_comm] using hpast_le j)
      (hasSum_scaled_geometric_shift (s i).radius 2).summable
  exact ht.trans_lt (htsum.trans_lt (half_lt_self (s i).radius_pos))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_SmoothLimit_SpherePersistentLimitMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

theorem sphere_persistent_limit_implies_main {r delta : ℝ}
    (s : (k : ℕ) → SphereNodalStage r delta k) (hN : ∀ k, k+1 ≤ (s k).frequency)
    (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (hnear : ∀ k, sphereCoefficientDistance (s k).charts 8
      (s k).energy.tensor (s k).energy.density b.tensor b.density < (s k).radius) :
    MainTarget := by
  have H (k : ℕ) := (s k).persistence b hb (hnear k)
  choose mu v hwindow hmu hv hv0 he hlift hln hle hratio using H
  exact mainTarget_of_seed_windows
    (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
    (fun k ↦ (s k).frequency) mu (fun k ↦ circleLift (v k)) hN hmu
    (fun k ↦ (hwindow k).1) hln hlift hle hratio

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target

theorem yau_nodal_set_upper_bound_counterexample_oai : MainTarget := by
  obtain ⟨r,delta,s,hfreq,b,hb,hnear⟩ := sphere_iteration_positive_limit
  exact sphere_persistent_limit_implies_main s hfreq b hb hnear

end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample_oai := @OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample_oai
