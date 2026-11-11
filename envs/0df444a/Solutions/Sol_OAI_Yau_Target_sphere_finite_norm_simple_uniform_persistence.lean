-- Prove2me | solution 1 for OAI.Yau.Target.sphere_finite_norm_simple_uniform_persistence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:17.674235+00:00
-- url     : https://prove2.me/submissions/7d6d6552-5ca8-4cbf-9523-627257e881c9

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
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
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
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
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
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_C1_intrinsic_limit
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_indexed_compactness
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_indexed_eigenvalue_continuity

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Function Set
open scoped ContDiff
variable {n : ℕ}

theorem pairing_smooth {u : Coord n → ℝ} {V : Coord n → Coord n}
    (hu : ContDiff ℝ ∞ u) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (pairing u V) := by
  apply ContDiff.sum
  intro i _
  exact ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).mul (hV i)

theorem weightedDiv_smooth {gamma : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (weightedDiv gamma V) := by
  apply (hg.inv hgn).mul
  apply ContDiff.sum
  intro i _
  exact (((hg.mul (hV i)).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

end
end Yau

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteSmoothPartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped Topology ContDiff
noncomputable section

theorem sphere_finite_smooth_partition :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ p x, 0 ≤ theta p x) ∧ (∀ x, ∑ p, theta p x=1) ∧
      (∀ p, tsupport (theta p) ⊆ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) 1) ∧
      (∀ p, tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) 1) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) := by
  classical
  obtain ⟨P,hP⟩ := finite_sphere_coordinate_cover
  let U : {p // p ∈ P} → Set Base := fun p ↦ sphereChartCoordMap p.val '' ball (0 : Yau.Jets.Coord) 1
  have hcover : (univ : Set Base) ⊆ ⋃ p, U p := by
    intro x _
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,z,hz,hzx⟩
  obtain ⟨theta,hsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 4) isClosed_univ U
    (fun p ↦ sphereChartCoordMap_isOpenMap p.val _ isOpen_ball) hcover
  have hs (p : {p // p ∈ P}) :
      tsupport (theta p ∘ sphereChartCoordMap p.val) ⊆ closedBall (0 : Yau.Jets.Coord) 1 := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    obtain ⟨y,hy,he⟩ := hsub p (subset_closure hx)
    have hxy : y=x := sphereChartCoordMap_injective p.val he
    exact hxy ▸ ball_subset_closedBall hy
  refine ⟨P,(fun p ↦ theta p),(fun p ↦ (theta p).contMDiff),theta.nonneg,?_,hsub,hs,?_⟩
  · intro x
    have h := theta.sum_eq_one (mem_univ x)
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by simp)] at h
    exact h
  · intro p
    exact (isCompact_closedBall (0 : Yau.Jets.Coord) 1).of_isClosed_subset isClosed_closure (hs p)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactWeightedDivergenceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set MeasureTheory
open scoped ContDiff
noncomputable section
variable {d : ℕ}

lemma integral_directional_derivative_compact_zero (g : Coord d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (v : Coord d) :
    (∫ x, fderiv ℝ g x v) = 0 := by
  have hd : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ g x v) :=
    (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi : Integrable (fun x ↦ fderiv ℝ g x v) := hd.continuous.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Coord d ↦ (1:ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hi)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ ↦ differentiableAt_const 1) (fun x _ ↦ hg.differentiable (by simp) x)
  simpa using h

theorem integral_weightedDiv_compact_zero (gamma : Coord d → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (V : Coord d → Coord d) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*weightedDiv gamma V x) = 0 := by
  let W : Fin d → Coord d → ℝ := fun i x ↦ gamma x*V x i
  have hW (i : Fin d) : ContDiff ℝ ∞ (W i) := hg.mul (hV i)
  have hWc (i : Fin d) : HasCompactSupport (W i) := (hc i).mul_left
  have hd (i : Fin d) : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ (W i) x (Pi.single i 1)) :=
    ((hW i).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi (i : Fin d) : Integrable (fun x ↦ fderiv ℝ (W i) x (Pi.single i 1)) :=
    (hd i).continuous.integrable_of_hasCompactSupport ((hWc i).fderiv_apply ℝ (Pi.single i 1))
  have he : (fun x ↦ gamma x*weightedDiv gamma V x) =
      (fun x ↦ ∑ i, fderiv ℝ (W i) x (Pi.single i 1)) := by
    funext x
    simp only [weightedDiv,coordDiv,coordPartial,← mul_assoc,mul_inv_cancel₀ (hgn x),one_mul,W]
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i),?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp only [integral_directional_derivative_compact_zero _ (hW _) (hWc _),Finset.sum_const_zero]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactWeightedWeakEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem compact_weighted_integration_by_parts (gamma phi : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*pairing phi V x) = -(∫ x, gamma x*phi x*weightedDiv gamma V x) := by
  have hp : HasCompactSupport (pairing phi V) := by
    unfold pairing
    have h := HasCompactSupport.finset_sum
      (s := Finset.univ) (fun i _ ↦ (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
        (f' := fun x ↦ V x i))
    convert h using 1 <;> first | rfl | (ext x; simp [coordPartial])
  have hiP : Integrable (fun x ↦ gamma x*pairing phi V x) :=
    (hg.mul (pairing_smooth hphi hV)).continuous.integrable_of_hasCompactSupport hp.mul_left
  have hiD : Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) :=
    ((hg.mul hphi).mul (weightedDiv_smooth hg hgn hV)).continuous.integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  obtain ⟨_,hz⟩ := integral_weightedDiv_compact_zero gamma hg hgn
    (fun x i ↦ phi x*V x i) (fun i ↦ hphi.mul (hV i)) (fun _ ↦ hc.mul_right)
  have he : (fun x ↦ gamma x*weightedDiv gamma (fun y i ↦ phi y*V y i) x) =
      (fun x ↦ gamma x*phi x*weightedDiv gamma V x + gamma x*pairing phi V x) := by
    funext x
    rw [weightedDiv_mul (hg.differentiable (by simp) x) (hgn x)
      (hphi.differentiable (by simp) x) (fun i ↦ (hV i).differentiable (by simp) x)]
    ring
  rw [he,integral_add hiD hiP] at hz
  exact ⟨hiP,hiD,by linarith⟩

theorem compact_weighted_weak_equation (gamma phi f : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (he : ∀ x, weightedDiv gamma V x + f x = 0) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*f x) ∧
    (∫ x, gamma x*pairing phi V x) = ∫ x, gamma x*phi x*f x := by
  obtain ⟨hiP,hiD,hid⟩ := compact_weighted_integration_by_parts gamma phi hg hgn hphi hc V hV
  have heq : (fun x ↦ gamma x*phi x*f x) =
      -(fun x ↦ gamma x*phi x*weightedDiv gamma V x) := by
    funext x
    have hx := he x
    simp only [Pi.neg_apply]
    rw [show f x = -weightedDiv gamma V x by linarith]
    ring
  rw [heq]
  refine ⟨hiP,hiD.neg,?_⟩
  change (∫ x, gamma x*pairing phi V x) = ∫ x, -(gamma x*phi x*weightedDiv gamma V x)
  rw [integral_neg]
  exact hid

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicRealCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma real_seedCoordPartial_pullback (f : BaseModel → ℝ) (i : Fin 4) (x : Yau.Jets.Coord) :
    Yau.coordPartial (f ∘ seedCoordEquiv) x i =
      fderiv ℝ f (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  unfold Yau.coordPartial
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma intrinsicRealFlux_pullback (A : IntrinsicTensor) (w : Base → ℝ) (p : Base) (i : Fin 4) :
    intrinsicRoundFlux A w p i ∘ seedCoordEquiv =
      fun x ↦ roundCoordDensity x * ∑ j,
        intrinsicRealPrincipal A p x i j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j := by
  funext x
  have hd (j : Fin 4) := real_seedCoordPartial_pullback (w ∘ (extChartAt (𝓡 4) p).symm) j x
  change ∀ j, Yau.coordPartial (w ∘ sphereChartCoordMap p) x j = _ at hd
  simp only [Function.comp_apply,intrinsicRoundFlux,← hd,intrinsicRealPrincipal]
  rw [show roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x by
    simp only [roundCoordDensity,roundChartDensity_conformal]]

theorem intrinsicRealOperator_pullback (A : IntrinsicTensor) (rho w : Base → ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicWeightedChartOperator A rho w p (seedCoordEquiv x) =
      (rho (sphereChartCoordMap p x))⁻¹ * Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
          Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x := by
  unfold intrinsicWeightedChartOperator Yau.weightedDiv Yau.coordDiv
  have hg : roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x := by
    simp only [roundCoordDensity,roundChartDensity_conformal]
  rw [hg,mul_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_seedCoordPartial_pullback, intrinsicRealFlux_pullback]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicCompactWeakEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsicRealVector_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (fun y ↦ ∑ j, intrinsicRealPrincipal A p y i j*
      Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) :=
  ContDiff.sum (fun j _ ↦ (intrinsicRealPrincipal_smooth A hA hs hp p i j).mul
    (real_coordPartial_smooth _ (spherePullback_smooth w hw p) j))

lemma intrinsic_real_divergence_equation (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrp : ∀ p, 0 < rho p) (w : Base → ℝ) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base) (x : Yau.Jets.Coord) :
    Yau.weightedDiv roundCoordDensity
      (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x +
      intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x) = 0 := by
  have h := he p (seedCoordEquiv x)
  rw [intrinsicRealOperator_pullback] at h
  change -((rho (sphereChartCoordMap p x))⁻¹ * _) = lam*w (sphereChartCoordMap p x) at h
  have hmul := congrArg (fun t : ℝ ↦ rho (sphereChartCoordMap p x)*t) h
  rw [mul_neg,← mul_assoc,mul_inv_cancel₀ (hrp _).ne',one_mul] at hmul
  dsimp [intrinsicRealPotential]
  linarith

theorem intrinsic_compact_weak_equation (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base)
    (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (fun x ↦ roundCoordDensity x *
      ∑ i, ∑ j, Yau.coordPartial phi x i*intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) ∧
    Integrable (fun x ↦ roundCoordDensity x*phi x*
      (intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x))) ∧
    (∫ x, roundCoordDensity x * ∑ i, ∑ j,
      Yau.coordPartial phi x i*intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) =
    ∫ x, roundCoordDensity x*phi x*(intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x)) := by
  have h := compact_weighted_weak_equation roundCoordDensity phi
    (fun x ↦ intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x))
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hphi hc
    (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
      Yau.coordPartial (w ∘ sphereChartCoordMap p) y j)
    (intrinsicRealVector_smooth A hA hs hp w hw p)
    (intrinsic_real_divergence_equation A rho hrp w lam he p)
  simpa only [Yau.pairing,Finset.mul_sum,mul_assoc] using h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicEnergyFiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma sphere_differential_pair_finite_sum {ι : Type*} [Fintype ι]
    (A : IntrinsicTensor) (f : ι → Base → ℝ) (g v : Base → ℝ)
    (hf : ∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f k))
    (hg : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ g) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (he : ∀ x, ∑ k, f k x = g x) (x : Base) :
    (∑ k, A x (sphereDifferential (f k) x) (sphereDifferential v x)) =
      A x (sphereDifferential g x) (sphereDifferential v x) := by
  classical
  have hd (y : Yau.Jets.Coord) (i : Fin 4) :
      Yau.coordPartial (g ∘ sphereChartCoordMap x) y i =
        ∑ k, Yau.coordPartial (f k ∘ sphereChartCoordMap x) y i := by
    have heq : g ∘ sphereChartCoordMap x = fun z ↦ ∑ k, (f k ∘ sphereChartCoordMap x) z := by
      funext z
      exact (he _).symm
    rw [heq]
    unfold Yau.coordPartial
    rw [fderiv_fun_sum (fun k _ ↦ (spherePullback_smooth (f k) (hf k) x).differentiable (by simp) y)]
    simp
  have hchart (y : Yau.Jets.Coord) :
      (∑ k, A (sphereChartCoordMap x y)
        (sphereDifferential (f k) (sphereChartCoordMap x y))
        (sphereDifferential v (sphereChartCoordMap x y))) =
      A (sphereChartCoordMap x y) (sphereDifferential g (sphereChartCoordMap x y))
        (sphereDifferential v (sphereChartCoordMap x y)) := by
    simp_rw [intrinsic_differential_pair_chart A _ v (hf _) hv,
      intrinsic_differential_pair_chart A g v hg hv,hd,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  have h := hchart 0
  rw [sphereChartCoordMap_zero] at h
  exact h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicGreenTesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

lemma intrinsic_green_compact_chart_test (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (hc : HasCompactSupport (u ∘ sphereChartCoordMap p)) :
    (∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rho u v := by
  have hw := (intrinsic_compact_weak_equation A hA hs hp rho hrp v hv lam he p
    (u ∘ sphereChartCoordMap p) (spherePullback_smooth u hu p) hc).2.2
  rw [sphereReferenceMeasure_integral_chart p,sphereWeightedPairing,
    sphereReferenceMeasure_integral_chart p,← integral_const_mul]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  rw [hw]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [Function.comp_apply,intrinsicRealPotential]
    ring)

theorem intrinsic_green_eigenfunction_test (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z)) :
    Integrable (fun x ↦ A x (sphereDifferential u x) (sphereDifferential v x)) sphereReferenceMeasure ∧
    Integrable (fun x ↦ rho x*u x*v x) sphereReferenceMeasure ∧
    (∫ x, A x (sphereDifferential u x) (sphereDifferential v x) ∂sphereReferenceMeasure) =
      lam*sphereWeightedPairing rho u v := by
  classical
  refine ⟨intrinsic_differential_pair_integrable A hA hs hp u v hu hv,
    sphereWeightedPairing_integrable rho u v hr.continuous hu.continuous hv.continuous,?_⟩
  obtain ⟨P,theta,htheta,_,hsum,_,_,hcompact⟩ := sphere_finite_smooth_partition
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ theta p x*u x
  have hf (p : {p // p ∈ P}) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f p) := (htheta p).mul hu
  have hsumf (x : Base) : ∑ p, f p x = u x := by
    simp only [f,← Finset.sum_mul,hsum,one_mul]
  have hlocal (p : {p // p ∈ P}) := intrinsic_green_compact_chart_test A hA hs hp rho hrp
    (f p) v (hf p) hv lam he p.val ((hcompact p).mul_right)
  calc
    _ = ∫ x, ∑ p, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (sphere_differential_pair_finite_sum A f u v hf hu hv hsumf x).symm)
    _ = ∑ p, ∫ x, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure :=
      integral_finsetSum _ (fun p _ ↦ intrinsic_differential_pair_integrable A hA hs hp (f p) v (hf p) hv)
    _ = lam*(∑ p, sphereWeightedPairing rho (f p) v) := by simp only [hlocal,Finset.mul_sum]
    _ = lam*sphereWeightedPairing rho u v := by
      congr 1
      unfold sphereWeightedPairing
      rw [← integral_finsetSum _ (fun p _ ↦ sphereWeightedPairing_integrable rho (f p) v
        hr.continuous (hf p).continuous hv.continuous)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        change (∑ p, rho x*f p x*v x) = rho x*u x*v x
        rw [← Finset.sum_mul,← Finset.mul_sum,hsumf])

end
end Yau.Target

end OAI
end

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

local instance sphereEnergyL2MapMeasurable_re950de_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_re950de_1 : BorelSpace Base := ⟨rfl⟩
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

theorem sphereEnergyL2Map_apply_norm_le (d : SphereEnergyData) (u : SphereEnergyHilbert d) :
    ‖sphereEnergyL2Map d u‖ ≤ ‖u‖ := by
  have h := (sphereEnergyL2Map d).le_opNorm u
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right (sphereEnergyL2Map_norm_le d) (norm_nonneg u))

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

lemma sphereCoefficientDistance_nonneg (P : Finset Base) (J : ℕ)
    (A B : IntrinsicTensor) (rho sigma : Base → ℝ)
    (hA : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient A rho p))
    (hB : ∀ p ∈ P, ContDiff ℝ ∞ (intrinsicChartCoefficient B sigma p)) :
    0 ≤ sphereCoefficientDistance P J A rho B sigma :=
  finiteChartDerivativeSize_nonneg P sphereAtlasCore_compact J _ (fun p hp ↦ (hB p hp).sub (hA p hp))

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

local instance sphereWeakResolventMeasurable_re950de_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_re950de_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereCompletedDirichlet_coe (d : SphereEnergyData) (u v : SphereEnergySmooth d) :
    sphereCompletedDirichlet d (sphereEnergyToCompletion d u) (sphereEnergyToCompletion d v) =
      sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) := by
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,sphereEnergyL2Map_coe]
  have hinner : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d v) =
      sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) :=
    sphereWeightedToLp_inner d.density d.continuous (fun x ↦ (d.positive x).le) _ _
      (SphereEnergySmooth.toSmooth d u).property.continuous (SphereEnergySmooth.toSmooth d v).property.continuous
  rw [hinner,(sphereEnergyToCompletion d).inner_map_map]
  change (sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)+
    sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v))-
    sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v) = _
  ring

theorem sphereCompletedDirichlet_nonneg (d : SphereEnergyData) (u : SphereEnergyHilbert d) :
    0 ≤ sphereCompletedDirichlet d u u := by
  rw [sphereCompletedDirichlet,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith [sphereEnergyL2Map_apply_norm_le d u,norm_nonneg u,norm_nonneg (sphereEnergyL2Map d u)]

theorem sphereWeakSolution_spec (d : SphereEnergyData) (f : SphereWeightedL2 d) (v : SphereEnergyHilbert d) :
    inner ℝ (sphereWeakSolution d f) v = inner ℝ f (sphereEnergyL2Map d v) :=
  (sphereEnergyL2Map d).adjoint_inner_left v f

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereVariationalResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold
open scoped ContDiff
noncomputable section

local instance sphereVariationalResolventMeasurable_re950de_1 : MeasurableSpace Base := borel Base
local instance sphereVariationalResolventBorel_re950de_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_variational_eigenvalue_nonneg (d : SphereEnergyData) (lam : ℝ)
    (z : SphereEnergyHilbert d) (hz : sphereEnergyL2Map d z ≠ 0)
    (he : ∀ v, sphereCompletedDirichlet d z v =
      lam*inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d v)) : 0 ≤ lam := by
  have h := sphereCompletedDirichlet_nonneg d z
  rw [he z,real_inner_self_eq_norm_sq] at h
  exact (mul_nonneg_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hz))).mp h

theorem sphere_variational_eigen_to_resolvent (d : SphereEnergyData) (lam : ℝ)
    (z : SphereEnergyHilbert d) (hz : sphereEnergyL2Map d z ≠ 0)
    (he : ∀ v, sphereCompletedDirichlet d z v =
      lam*inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d v)) :
    z = (lam+1) • sphereWeakSolution d (sphereEnergyL2Map d z) ∧
    sphereL2Resolvent d (sphereEnergyL2Map d z) = (lam+1)⁻¹ • sphereEnergyL2Map d z := by
  have hlam : 0 < lam+1 := by linarith [sphere_variational_eigenvalue_nonneg d lam z hz he]
  have heq : z = (lam+1) • sphereWeakSolution d (sphereEnergyL2Map d z) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_smul_left_eq_smul,smul_eq_mul,sphereWeakSolution_spec]
    have h := he v
    dsimp [sphereCompletedDirichlet] at h
    linarith
  refine ⟨heq,?_⟩
  have h := congrArg (sphereEnergyL2Map d) heq
  rw [map_smul] at h
  change sphereEnergyL2Map d z = (lam+1) • sphereL2Resolvent d (sphereEnergyL2Map d z) at h
  conv_rhs => rw [h,smul_smul,inv_mul_cancel₀ hlam.ne',one_smul]

theorem sphere_smooth_intrinsic_eigen_to_variational (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (u : SphereEnergySmooth d) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*((SphereEnergySmooth.toSmooth d u : Base → ℝ)) ((extChartAt (𝓡 4) p).symm z)) :
    ∀ v : SphereEnergyHilbert d,
      sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
        lam*inner ℝ (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) (sphereEnergyL2Map d v) := by
  intro v
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun v ↦ sphereCompletedDirichlet d (sphereEnergyToCompletion d u) v =
      lam*inner ℝ (sphereEnergyL2Map d (sphereEnergyToCompletion d u)) (sphereEnergyL2Map d v)) v
  · apply isClosed_eq
    · exact (continuous_const.inner continuous_id).sub
        (continuous_const.inner (sphereEnergyL2Map d).continuous)
    · fun_prop
  · intro w
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe,sphereEnergyL2Map_coe]
    have hinner : inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Linear d w) =
        sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d w) :=
      sphereWeightedToLp_inner _ d.continuous (fun x ↦ (d.positive x).le) _ _
        (SphereEnergySmooth.toSmooth d u).property.continuous (SphereEnergySmooth.toSmooth d w).property.continuous
    rw [hinner,sphereDirichletForm_symm d.tensor d.symm]
    have h := (intrinsic_green_eigenfunction_test d.tensor d.smooth d.symm d.pos d.density hr d.positive
      (SphereEnergySmooth.toSmooth d w) (SphereEnergySmooth.toSmooth d u)
      (SphereEnergySmooth.toSmooth d w).property (SphereEnergySmooth.toSmooth d u).property lam he).2.2
    simpa only [sphereDirichletForm,sphereWeightedPairing_symm d.density (SphereEnergySmooth.toSmooth d w)
      (SphereEnergySmooth.toSmooth d u)] using h

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

theorem sphere_finite_norm_indexed_eigenvalue_convergence (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x)
    (d : SphereEnergyData) (b : ℕ → SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) (J N : ℕ)
    (ht : Tendsto (fun j ↦ sphereCoefficientDistance P J d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereIndexedEigenvalue (b j) N) atTop (𝓝 (sphereIndexedEigenvalue d N)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨eta,heta,H⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d hd N eps heps
  filter_upwards [ht.eventually (gt_mem_nhds heta)] with j hj
  simpa only [Real.dist_eq] using H (b j) (hb j)
    ((sphereCoefficientDistance_mono_order P d (b j) hd (hb j) 0 J (Nat.zero_le J)).trans_lt hj)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereVariationalContinuousRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereContinuousRegularityMeasurable_re950de_1 : MeasurableSpace Base := borel Base
local instance sphereContinuousRegularityBorel_re950de_1 : BorelSpace Base := ⟨rfl⟩
lemma sphere_continuous_eq_of_weighted_ae (d : SphereEnergyData) (u v : Base → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (ha : u =ᵐ[sphereWeightedMeasure d.density] v) : u=v := by
  let := sphereReferenceMeasure_openPos
  exact Measure.eq_of_ae_eq ((sphereWeightedMeasure_ae_iff d _).mp ha) hu hv

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

open Manifold Yau.Geometry Filter
open scoped ContDiff Topology

theorem sphere_finite_norm_lower_order_convergence (P : Finset Base)
    (d : SphereEnergyData) (b : ℕ → SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (J K : ℕ) (hJK : J ≤ K)
    (ht : Tendsto (fun j ↦ sphereCoefficientDistance P K d.tensor d.density
      (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereCoefficientDistance P J d.tensor d.density
      (b j).tensor (b j).density) atTop (𝓝 0) := by
  apply squeeze_zero _ _ ht
  · intro j
    exact sphereCoefficientDistance_nonneg P J d.tensor (b j).tensor d.density (b j).density
      (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
      (fun p _ ↦ intrinsic_coefficient_chart_smooth (b j).tensor (b j).smooth (b j).symm (b j).pos
        (b j).density (hb j) p)
  · intro j
    exact sphereCoefficientDistance_mono_order P d (b j) hd (hb j) J K hJK

end Yau.Target

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteNormIntrinsicCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section

local instance sphereIntrinsicCompactMeasurable_re950de_1 : MeasurableSpace Base := borel Base
local instance sphereIntrinsicCompactBorel_re950de_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_norm_indexed_intrinsic_compactness (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (N : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) (1/512), sphereChartCoordMap p y=x) ∧
      ∃ eta > 0, ∀ (b : ℕ → SphereEnergyData),
        (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) →
        (∀ j, sphereCoefficientDistance P 8 d.tensor d.density (b j).tensor (b j).density < eta) →
        Tendsto (fun j ↦ sphereCoefficientDistance P 8 d.tensor d.density
          (b j).tensor (b j).density) atTop (𝓝 0) →
        ∀ u : ℕ → Base → ℝ,
          (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) →
          (∀ j, sphereWeightedPairing (b j).density (u j) (u j)=1) →
          (∀ j p y, -intrinsicWeightedChartOperator (b j).tensor (b j).density (u j) p y =
            sphereIndexedEigenvalue (b j) N * u j ((extChartAt (𝓡 4) p).symm y)) →
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
            sphereWeightedPairing d.density v v=1 ∧ v ≠ 0 ∧
            (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
              sphereIndexedEigenvalue d N * v ((extChartAt (𝓡 4) p).symm y)) ∧
            ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
              ∀ p ∈ P, ∀ i : Fin 4,
                TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) [i])
                  (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 (1/256)) := by
  obtain ⟨P,hP,eta,heta,H⟩ := sphere_finite_norm_indexed_compactness d hd N 2
  refine ⟨P,hP,eta,heta,?_⟩
  intro b hb hdist hcoeff u hu hn he
  let U (j : ℕ) : SphereEnergySmooth (b j) := (⟨u j,hu j⟩ : sphereSmoothFunctions)
  let f (j : ℕ) : SphereWeightedL2 (b j) := sphereEnergyL2Linear (b j) (U j)
  have hfn (j : ℕ) : ‖f j‖=1 := by
    have h := sphereEnergyL2Linear_norm_sq (b j) (U j)
    change ‖f j‖^2=sphereWeightedPairing (b j).density (u j) (u j) at h
    rw [hn j] at h
    nlinarith [norm_nonneg (f j)]
  have hfe (j : ℕ) : sphereL2Resolvent (b j) (f j) =
      (sphereIndexedEigenvalue (b j) N+1)⁻¹ • f j := by
    have hnonzero : sphereEnergyL2Map (b j) (sphereEnergyToCompletion (b j) (U j)) ≠ 0 := by
      rw [sphereEnergyL2Map_coe]
      intro hz
      have hh := hfn j
      change ‖sphereEnergyL2Linear (b j) (U j)‖=1 at hh
      rw [hz,norm_zero] at hh
      norm_num at hh
    have h := (sphere_variational_eigen_to_resolvent (b j) (sphereIndexedEigenvalue (b j) N)
      (sphereEnergyToCompletion (b j) (U j)) hnonzero
      (sphere_smooth_intrinsic_eigen_to_variational (b j) (hb j) (U j) _ (he j))).2
    simpa only [sphereEnergyL2Map_coe] using h
  obtain ⟨u',hu',ha,_,_,v,hv,nu,hnu,ht,hjet,hnorm⟩ := H b hb hdist f hfe hfn
  have hsame : u'=u := by
    funext j
    apply sphere_continuous_eq_of_weighted_ae (b j) (u' j) (u j) (hu' j).continuous (hu j).continuous
    exact (ha j).trans (sphereWeighted_memLp (b j).density (b j).continuous
      (fun x ↦ ((b j).positive x).le) (u j) (hu j).continuous).coeFn_toLp
  subst u'
  have hvnorm := hnorm hcoeff
  have hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) (1/256), sphereChartCoordMap p y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hP x
    exact ⟨p,hp,y,(ball_subset_ball (by norm_num : (1:ℝ)/512 ≤ 1/256)) hy,hyx⟩
  have hcore : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hP x
    exact ⟨p,hp,seedCoordEquiv y,⟨y,(closedBall_subset_closedBall (by norm_num : (1:ℝ)/512 ≤ 1))
      (ball_subset_closedBall hy),rfl⟩,hyx⟩
  have h0 := sphere_finite_norm_lower_order_convergence P d b hd hb 0 8 (by omega) hcoeff
  have hlam := sphere_finite_norm_indexed_eigenvalue_convergence P hcore d b hd hb 8 N hcoeff
  let V (j : ℕ) : SphereEnergySmooth d := (⟨u (nu j),hu (nu j)⟩ : sphereSmoothFunctions)
  have hreg := sphere_finite_norm_C1_intrinsic_limit P (1/256) (by norm_num) hcover d hd
    (fun j ↦ b (nu j)) (fun j ↦ hb (nu j)) V v hv.continuous hvnorm.2 ht
    (fun p hp i ↦ hjet p hp [i] (by simp))
    (h0.comp hnu.tendsto_atTop) (fun j ↦ sphereIndexedEigenvalue (b (nu j)) N)
    (sphereIndexedEigenvalue d N) (hlam.comp hnu.tendsto_atTop) (fun j ↦ he (nu j))
  exact ⟨v,hreg.1,hvnorm.1,hvnorm.2,hreg.2,nu,hnu,ht,fun p hp i ↦ hjet p hp [i] (by simp)⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereNormalizedSimpleUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

lemma sphereWeightedPairing_smul_self (rho u : Base → ℝ) (c : ℝ) :
    sphereWeightedPairing rho (c • u) (c • u)=c^2*sphereWeightedPairing rho u u := by
  rw [sphereWeightedPairing_smul_left,sphereWeightedPairing_symm rho u (c • u),sphereWeightedPairing_smul_left]
  ring

theorem sphere_normalized_simple_eigenfunction_signed (d : SphereEnergyData)
    (u : Base → ℝ) (hun : sphereWeightedPairing d.density u u=1) (lam : ℝ)
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u)
    (v : Base → ℝ) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hvn : sphereWeightedPairing d.density v v=1)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
      lam*v ((extChartAt (𝓡 4) p).symm y)) : v=u ∨ v=-u := by
  obtain ⟨c,rfl⟩ := hsimple v hv he
  rw [sphereWeightedPairing_smul_self,hun,mul_one] at hvn
  have hc : c=1 ∨ c=-1 := by
    have h : (c-1)*(c+1)=0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    · right; linarith
  rcases hc with rfl | rfl <;> simp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_SphereSimpleUniformPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry
open scoped ContDiff Topology
noncomputable section

theorem sphere_finite_norm_simple_uniform_persistence_oai (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (N : ℕ)
    (u : Base → ℝ) (hun : sphereWeightedPairing d.density u u=1)
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        sphereIndexedEigenvalue d N*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) (1/512), sphereChartCoordMap p y=x) ∧
      ∀ eps > 0, ∃ eta > 0, ∀ b : SphereEnergyData,
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
        sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
        ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
          sphereWeightedPairing b.density v v=1 →
          (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
            sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) →
          (∀ x, |v x-u x| < eps) ∨ (∀ x, |v x+u x| < eps) := by
  classical
  obtain ⟨P,hP,eta₀,heta₀,H⟩ := sphere_finite_norm_indexed_intrinsic_compactness d hd N
  refine ⟨P,hP,?_⟩
  intro eps heps
  let Good (v : Base → ℝ) : Prop := (∀ x, |v x-u x| < eps) ∨ (∀ x, |v x+u x| < eps)
  change ∃ eta > 0, ∀ b : SphereEnergyData,
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
    sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
    ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      sphereWeightedPairing b.density v v=1 →
      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
        sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) → Good v
  by_contra hbad
  push Not at hbad
  choose b hb hdist v hv hn he hbad using
    (fun j : ℕ ↦ hbad (min eta₀ (1/((j:ℝ)+1))) (lt_min heta₀ (by positivity)))
  have hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 8 d.tensor d.density
      (b j).tensor (b j).density) atTop (𝓝 0) := by
    apply squeeze_zero _ _ tendsto_one_div_add_atTop_nhds_zero_nat
    · intro j
      exact sphereCoefficientDistance_nonneg P 8 d.tensor (b j).tensor d.density (b j).density
        (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
        (fun p _ ↦ intrinsic_coefficient_chart_smooth (b j).tensor (b j).smooth (b j).symm (b j).pos
          (b j).density (hb j) p)
    · intro j
      exact (hdist j).le.trans (min_le_right _ _)
  obtain ⟨v₀,hv₀,hn₀,_,he₀,nu,hnu,ht,_⟩ := H b hb
    (fun j ↦ (hdist j).trans_le (min_le_left _ _)) hcoeff v hv hn he
  have hsigned := sphere_normalized_simple_eigenfunction_signed d u hun (sphereIndexedEigenvalue d N)
    hsimple v₀ hv₀ hn₀ he₀
  have hc := (Metric.tendstoUniformly_iff.mp ht) eps heps
  obtain ⟨j,hj⟩ := hc.exists
  apply hbad (nu j)
  rcases hsigned with rfl | rfl
  · left
    intro x
    simpa only [Real.dist_eq,abs_sub_comm] using hj x
  · right
    intro x
    simpa only [Pi.neg_apply,Real.dist_eq,abs_sub_comm,sub_neg_eq_add] using hj x

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_finite_norm_simple_uniform_persistence_oai := @OAI.Yau.Target.sphere_finite_norm_simple_uniform_persistence_oai
