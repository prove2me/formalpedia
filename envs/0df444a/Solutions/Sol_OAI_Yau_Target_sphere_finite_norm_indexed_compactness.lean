-- Prove2me | solution 1 for OAI.Yau.Target.sphere_finite_norm_indexed_compactness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:51.482653+00:00
-- url     : https://prove2.me/submissions/04984af3-e8b0-42da-9c94-f5b45ea7df8a

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
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_eigen_global_neighborhood_compactness
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_indexed_eigenvalue_continuity
import Theorems.Thm_OAI_Yau_Target_sphere_resolvent_finite_smooth_frame

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

lemma matrixContravariant_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ)
    (α : BaseModel →L[ℝ] ℝ) :
    WithLp.ofLp (matrixContravariant A α) = A *ᵥ baseCovectorCoordinates α := by
  ext k
  simp [matrixContravariant,baseCovectorCoordinates,mulVec,dotProduct,
    EuclideanSpace.basisFun_apply,Pi.single_apply,ite_mul,mul_ite,mul_comm]

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

end
end Yau

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothGreenLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphere_smooth_green_compact_chart (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base)
    (hc : HasCompactSupport (u ∘ sphereChartCoordMap p)) :
    Integrable (fun x ↦ roundCoordDensity x*(u (sphereChartCoordMap p x))*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) ∧
    sphereDirichletForm A u v = -(∫ x, roundCoordDensity x*(u (sphereChartCoordMap p x))*
      Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p) x) := by
  have h := Yau.compact_weighted_integration_by_parts roundCoordDensity
    (u ∘ sphereChartCoordMap p) roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
    (spherePullback_smooth u hu p) hc (sphereChartFlux A v p)
    (intrinsicRealVector_smooth A hA hs hp v hv p)
  refine ⟨h.2.1,?_⟩
  rw [sphereDirichletForm,sphereReferenceMeasure_integral_chart p]
  simp only [roundChartDensity_coord_eq,intrinsic_differential_pair_chart A u v hu hv]
  simpa only [Yau.pairing,sphereChartFlux,Function.comp_apply,Finset.mul_sum,mul_assoc] using h.2.2

theorem sphere_smooth_green_finite_partition (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) :
    ∃ (P : Finset Base) (theta : {p // p ∈ P} → Base → ℝ),
      (∀ p, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (theta p)) ∧
      (∀ x, ∑ p, theta p x = 1) ∧
      (∀ p, HasCompactSupport (theta p ∘ sphereChartCoordMap p.val)) ∧
      ∀ u v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
        sphereDirichletForm A u v = -(∑ p, ∫ x, roundCoordDensity x*
          (theta p (sphereChartCoordMap p.val x)*u (sphereChartCoordMap p.val x))*
          Yau.weightedDiv roundCoordDensity (sphereChartFlux A v p.val) x) := by
  classical
  obtain ⟨P,theta,htheta,_,hsum,_,_,hcompact⟩ := sphere_finite_smooth_partition
  refine ⟨P,theta,htheta,hsum,hcompact,?_⟩
  intro u v hu hv
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ theta p x*u x
  have hf (p : {p // p ∈ P}) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (f p) := (htheta p).mul hu
  have hsumf (x : Base) : ∑ p, f p x = u x := by
    simp only [f,← Finset.sum_mul,hsum,one_mul]
  have he (p : {p // p ∈ P}) :=
    (sphere_smooth_green_compact_chart A hA hs hp (f p) v (hf p) hv p.val ((hcompact p).mul_right)).2
  calc
    _ = ∫ x, ∑ p, A x (sphereDifferential (f p) x) (sphereDifferential v x) ∂sphereReferenceMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ (sphere_differential_pair_finite_sum A f u v hf hu hv hsumf x).symm)
    _ = ∑ p, sphereDirichletForm A (f p) v :=
      integral_finsetSum _ (fun p _ ↦ intrinsic_differential_pair_integrable A hA hs hp (f p) v (hf p) hv)
    _ = _ := by simp only [he,Finset.sum_neg_distrib,f]

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

local instance sphereEnergyL2MapMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereWeightedL1Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereWeightedL1BoundMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereWeightedL1BoundBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_reference_L1_bound (d : SphereEnergyData) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ u : SphereEnergySmooth d,
      (∫ x, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ∂sphereReferenceMeasure) ≤
        B*‖sphereEnergyL2Linear d u‖ := by
  have hi : Continuous (fun x ↦ (d.density x)⁻¹) := d.continuous.inv₀ (fun x ↦ (d.positive x).ne')
  let g := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) _ hi
  refine ⟨‖g‖,norm_nonneg _,?_⟩
  intro u
  let f : Base → ℝ := fun x ↦ |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x|
  have hf : Continuous f := (SphereEnergySmooth.toSmooth d u).property.continuous.abs
  let L := sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) f hf
  have hn : ‖L‖ = ‖sphereEnergyL2Linear d u‖ := by
    have hL := sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le) f hf
    have hu := sphereEnergyL2Linear_norm_sq d u
    have he : sphereWeightedPairing d.density f f =
        sphereWeightedPairing d.density (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by
        dsimp [f]
        simp only [mul_assoc,← sq,sq_abs])
    rw [he] at hL
    change ‖L‖^2 = _ at hL
    nlinarith [norm_nonneg L,norm_nonneg (sphereEnergyL2Linear d u)]
  have he : inner ℝ L g = ∫ x, f x ∂sphereReferenceMeasure := by
    rw [sphereWeightedToLp_inner]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x ↦ by
      change d.density x*f x*(d.density x)⁻¹ = f x
      field_simp [(d.positive x).ne'])
  have h := real_inner_le_norm L g
  rw [he,hn] at h
  exact h.trans_eq (mul_comm _ _)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereSmoothGreenBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

local instance sphereSmoothGreenBoundMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothGreenBoundBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_smooth_dirichlet_L1_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SphereEnergySmooth d,
      |sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)| ≤
        C*(∫ x, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ∂sphereReferenceMeasure) := by
  classical
  obtain ⟨P,theta,htheta,_,hc,hgreen⟩ := sphere_smooth_green_finite_partition d.tensor d.smooth d.symm d.pos
  let I := {p // p ∈ P}
  let G : I → Yau.Jets.Coord → ℝ := fun p x ↦ theta p (sphereChartCoordMap p.val x)*
    Yau.weightedDiv roundCoordDensity (sphereChartFlux d.tensor (SphereEnergySmooth.toSmooth d v) p.val) x
  have hG (p : I) : Continuous (G p) :=
    (spherePullback_smooth (theta p) (htheta p) p.val).continuous.mul
      (Yau.weightedDiv_smooth roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
        (intrinsicRealVector_smooth d.tensor d.smooth d.symm d.pos (SphereEnergySmooth.toSmooth d v)
          (SphereEnergySmooth.toSmooth d v).property p.val)).continuous
  have hGc (p : I) : HasCompactSupport (G p) := (hc p).mul_right
  have hb (p : I) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |G p x| ≤ K := by
    obtain ⟨K,hK⟩ := (((hGc p).isCompact_range (hG p)).image continuous_norm).bddAbove
    refine ⟨max K 0,le_max_right _ _,fun x ↦ ?_⟩
    exact (hK ⟨G p x,⟨x,rfl⟩,rfl⟩).trans (le_max_left _ _)
  choose K hK hKb using hb
  refine ⟨∑ p, K p,Finset.sum_nonneg (fun p _ ↦ hK p),?_⟩
  intro u
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : Continuous f := (SphereEnergySmooth.toSmooth d u).property.continuous
  have hI (p : I) : Integrable (fun x ↦ roundCoordDensity x*|f (sphereChartCoordMap p.val x)|) := by
    simpa only [roundChartDensity_coord_eq] using
      (sphereReferenceMeasure_integrable_chart p.val (fun x ↦ |f x|)).mp
        (sphereReferenceMeasure_integrable_continuous _ hf.abs)
  have hterm (p : I) : |∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| ≤
      K p*(∫ x, |f x| ∂sphereReferenceMeasure) := by
    have hi : Integrable (fun x ↦ roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x) :=
      ((roundCoordDensity_smooth.continuous.mul (hf.comp (sphereChartCoordMap_smooth p.val).continuous)).mul (hG p)).integrable_of_hasCompactSupport
        (hGc p).mul_left
    calc
      _ ≤ ∫ x, ‖roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, K p*(roundCoordDensity x*|f (sphereChartCoordMap p.val x)|) := by
        apply integral_mono hi.norm ((hI p).const_mul (K p))
        intro x
        simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (roundCoordDensity_pos x)]
        nlinarith [mul_le_mul_of_nonneg_left (hKb p x)
          (mul_nonneg (roundCoordDensity_pos x).le (abs_nonneg (f (sphereChartCoordMap p.val x))))]
      _ = _ := by
        rw [integral_const_mul,sphereReferenceMeasure_integral_chart p.val]
        simp only [roundChartDensity_coord_eq]
  have hg := hgreen f (SphereEnergySmooth.toSmooth d v) (SphereEnergySmooth.toSmooth d u).property
    (SphereEnergySmooth.toSmooth d v).property
  rw [hg,abs_neg]
  calc
    _ = |∑ p : I, ∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by dsimp [G] <;> ring)
    _ ≤ ∑ p : I, |∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : I, K p*(∫ x, |f x| ∂sphereReferenceMeasure) :=
      Finset.sum_le_sum (fun p _ ↦ hterm p)
    _ = _ := by rw [Finset.sum_mul]

theorem sphere_smooth_dirichlet_L2_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SphereEnergySmooth d,
      |sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)| ≤
        C*‖sphereEnergyL2Linear d u‖ := by
  obtain ⟨C,hC,hb⟩ := sphere_smooth_dirichlet_L1_bound d v
  obtain ⟨B,hB,hL⟩ := sphere_reference_L1_bound d
  refine ⟨C*B,mul_nonneg hC hB,fun u ↦ ?_⟩
  exact (hb u).trans ((mul_le_mul_of_nonneg_left (hL u) hC).trans_eq (mul_assoc C B _).symm)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinatePartialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma partialJet_eq_iterated (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) (x : ι → ℝ) :
    partialJet f ds x = iteratedFDeriv ℝ ds.length f x (partialDirs ds) := by
  induction ds generalizing x with
  | nil => simp [partialJet,partialDirs,iteratedFDeriv_zero_apply]
  | cons i ds ih =>
    have hh : partialJet f ds = fun x ↦ iteratedFDeriv ℝ ds.length f x (partialDirs ds) :=
      funext ih
    change fderiv ℝ (partialJet f ds) x (Pi.single i 1) = _
    rw [hh]
    symm
    have hdiff := hf.differentiable_iteratedFDeriv (m := ds.length)
      (by exact_mod_cast (show (ds.length:ℕ∞) < ⊤ from WithTop.coe_lt_top _))
    simpa only [List.length_cons,partialDirs,Fin.cons_zero,Fin.tail_cons] using
      (hdiff x).iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single i 1) (partialDirs ds))

lemma partialDirs_norm_le_one (ds : List ι) : ‖partialDirs ds‖ ≤ 1 := by
  induction ds with
  | nil => exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun j ↦ Fin.elim0 j)
  | cons i ds ih =>
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] at ih ⊢
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change ‖(Pi.single i (1:ℝ) : ι → ℝ)‖ ≤ 1
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro k
      by_cases h : k = i <;> simp [h]
    · simpa [partialDirs] using ih k

end
end Yau.Analysis

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

local instance sphereWeakResolventMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
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

theorem sphereWeakSolution_spec (d : SphereEnergyData) (f : SphereWeightedL2 d) (v : SphereEnergyHilbert d) :
    inner ℝ (sphereWeakSolution d f) v = inner ℝ f (sphereEnergyL2Map d v) :=
  (sphereEnergyL2Map d).adjoint_inner_left v f

theorem sphereL2Resolvent_inner (d : SphereEnergyData) (f g : SphereWeightedL2 d) :
    inner ℝ (sphereL2Resolvent d f) g = inner ℝ (sphereWeakSolution d f) (sphereWeakSolution d g) := by
  exact ((sphereEnergyL2Map d).adjoint_inner_right (sphereWeakSolution d f) g).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereEnergyL2Injective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereEnergyL2InjectiveMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2InjectiveBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_completed_dirichlet_test_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SphereEnergyHilbert d,
      |sphereCompletedDirichlet d z (sphereEnergyToCompletion d v)| ≤ C*‖sphereEnergyL2Map d z‖ := by
  obtain ⟨C,hC,hb⟩ := sphere_smooth_dirichlet_L2_bound d v
  refine ⟨C,hC,?_⟩
  intro z
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun z ↦ |sphereCompletedDirichlet d z (sphereEnergyToCompletion d v)| ≤ C*‖sphereEnergyL2Map d z‖) z
  · apply isClosed_le
    · exact ((continuous_id.inner continuous_const).sub
        ((sphereEnergyL2Map d).continuous.inner continuous_const)).abs
    · fun_prop
  · intro u
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe]
    exact hb u

theorem sphereEnergyL2Map_eq_zero_iff (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    sphereEnergyL2Map d z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    apply (sphereEnergyToCompletion_dense d).induction_on (p := fun v ↦ inner ℝ z v = 0) z
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro v
      obtain ⟨C,_,hC⟩ := sphere_completed_dirichlet_test_bound d v
      have h := hC z
      rw [hz,norm_zero,mul_zero] at h
      have hd := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simpa only [sphereCompletedDirichlet,hz,inner_zero_left,sub_zero] using hd
  · rintro rfl
    exact map_zero _

theorem sphereEnergyL2Map_injective (d : SphereEnergyData) : Function.Injective (sphereEnergyL2Map d) := by
  apply (LinearMap.ker_eq_bot).mp
  ext z
  exact sphereEnergyL2Map_eq_zero_iff d z

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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

theorem coefficientPrincipalEntry_apply (A : IntrinsicTensor) (rho : Base → ℝ)
    (p : Base) (z : BaseModel) (i j : Fin 4) :
    coefficientPrincipalEntry i j (intrinsicChartCoefficient A rho p z) =
      intrinsicSphereChartTensor A p z i j := by
  change (matrixContravariant (intrinsicSphereChartTensor A p z) (EuclideanSpace.proj j)) i = _
  have h := congrFun (matrixContravariant_coordinates (intrinsicSphereChartTensor A p z)
    (EuclideanSpace.proj j)) i
  simpa [Matrix.mulVec,dotProduct,baseCovectorCoordinates,EuclideanSpace.basisFun_apply,
    Pi.single_apply] using h

theorem sphereCoefficientDistance_scalar_derivative_bound (P : Finset Base) (J : ℕ)
    (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (L : CoefficientPoint BaseModel →L[ℝ] ℝ)
    (p : Base) (hp : p ∈ P) (x : Yau.Jets.Coord) (hx : x ∈ Metric.closedBall 0 1)
    (k : ℕ) (hk : k ≤ J) :
    ‖iteratedFDeriv ℝ k (fun y ↦ L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y)-
      intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) x‖ ≤
      (‖L‖ * (max 1 ‖seedCoordEquiv.toContinuousLinearMap‖)^J) *
        sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  let F : BaseModel → CoefficientPoint BaseModel := fun z ↦
    intrinsicChartCoefficient b.tensor b.density p z-intrinsicChartCoefficient d.tensor d.density p z
  have hF : ContDiff ℝ ∞ F :=
    (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
  have hsize : ‖iteratedFDeriv ℝ k F (seedCoordEquiv x)‖ ≤
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density :=
    norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J _
      (fun q _ ↦ (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q).sub
        (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q))
      p hp k hk _ ⟨x,hx,rfl⟩
  have hkfin : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
  change ‖iteratedFDeriv ℝ k (L ∘ (F ∘ seedCoordEquiv.toContinuousLinearMap)) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hF.comp seedCoordEquiv.toContinuousLinearMap.contDiff).contDiffAt hkfin]
  apply (L.norm_compContinuousMultilinearMap_le _).trans
  rw [seedCoordEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hF x hkfin]
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k F (seedCoordEquiv x)) (fun _ ↦ seedCoordEquiv.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hcomp
  have hpow : ‖seedCoordEquiv.toContinuousLinearMap‖^k ≤ (max 1 ‖seedCoordEquiv.toContinuousLinearMap‖)^J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  have hnonneg : 0 ≤ sphereCoefficientDistance P J d.tensor d.density b.tensor b.density :=
    (norm_nonneg _).trans hsize
  have hbound := hcomp.trans (mul_le_mul hsize hpow (by positivity) hnonneg)
  exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg L)).trans_eq (by ring)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPartialJetLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section

theorem partialJet_sub {I : Type*} [Fintype I] [DecidableEq I]
    (f g : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ds : List I) (x : I → ℝ) :
    partialJet (fun y ↦ f y-g y) ds x = partialJet f ds x-partialJet g ds x := by
  rw [partialJet_eq_iterated _ (hf.sub hg),partialJet_eq_iterated f hf,partialJet_eq_iterated g hg]
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast
    (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  rfl

theorem partialJet_const_mul {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (a : ℝ) (ds : List I) (x : I → ℝ) :
    partialJet (fun y ↦ a*f y) ds x = a*partialJet f ds x := by
  rw [partialJet_eq_iterated _ (contDiff_const.mul hf),partialJet_eq_iterated f hf]
  change iteratedFDeriv ℝ ds.length (a • f) x (partialDirs ds) = _
  rw [iteratedFDeriv_const_smul_apply (hf.of_le (by exact_mod_cast
    (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  rfl

theorem partialJet_norm_le_iterated {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (ds : List I) (x : I → ℝ) :
    |partialJet f ds x| ≤ ‖iteratedFDeriv ℝ ds.length f x‖ := by
  rw [partialJet_eq_iterated f hf]
  have h := (iteratedFDeriv ℝ ds.length f x).le_opNorm (partialDirs ds)
  have hp : (∏ i : Fin ds.length, ‖partialDirs ds i‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
      (norm_le_pi_norm (partialDirs ds) i).trans (partialDirs_norm_le_one ds))
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ ds.length f x)))

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereWeightedCoefficientJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Metric
open scoped ContDiff
noncomputable section

theorem sphere_weighted_coefficient_scalar_jet_bound (J : ℕ)
    (L : CoefficientPoint BaseModel →L[ℝ] ℝ) :
    ∃ C > 0, ∀ (P : Finset Base) (d b : SphereEnergyData),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
      |partialJet (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y))) ds x-
        partialJet (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) ds x| ≤
        C * sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  obtain ⟨K,hK,hKb⟩ := compact_multiplier_frequency_bound roundCoordDensity roundCoordDensity_smooth
    (isCompact_closedBall (0 : Yau.Jets.Coord) 1) J
  let H := (‖L‖+1) * (max 1 ‖seedCoordEquiv.toContinuousLinearMap‖)^J
  have hH : 0 < H := by dsimp [H] <;> positivity
  refine ⟨K*H,mul_pos hK hH,?_⟩
  intro P d b hd hb p hp x hx ds hds
  have hdc := intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd
  have hbc := intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb
  let D := sphereCoefficientDistance P J d.tensor d.density b.tensor b.density
  have hD : 0 ≤ D := sphereCoefficientDistance_nonneg P J d.tensor b.tensor d.density b.density
    (fun q _ ↦ hdc q) (fun q _ ↦ hbc q)
  let F : Yau.Jets.Coord → ℝ := fun y ↦ L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y)-
    intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))
  have hF : ContDiff ℝ ∞ F := by
    simpa only [F,Function.comp_def] using
      (ContinuousLinearMap.contDiff L).comp (((hbc p).sub (hdc p)).comp seedCoordEquiv.contDiff)
  have hFb : ∀ k, k ≤ J → ‖iteratedFDeriv ℝ k F x‖ ≤ H*D := by
    intro k hk
    apply (sphereCoefficientDistance_scalar_derivative_bound P J d b hd hb L p hp x hx k hk).trans
    apply mul_le_mul_of_nonneg_right _ hD
    dsimp [H]
    gcongr
    linarith
  have hmult := hKb F hF 1 (H*D) le_rfl (mul_nonneg hH.le hD) 0 x hx
    (fun k hk ↦ by simpa only [one_pow,mul_one] using hFb k hk) ds.length hds
  simp only [one_pow,mul_one] at hmult
  have hsub : (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y))-
      roundCoordDensity y * L (intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) =
      fun y ↦ roundCoordDensity y * F y := by
    funext y
    simp only [F,map_sub,mul_sub]
  have hbs : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y))) := by
    simpa only [Function.comp_def] using roundCoordDensity_smooth.mul
      ((ContinuousLinearMap.contDiff L).comp ((hbc p).comp seedCoordEquiv.contDiff))
  have hds : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y * L (intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) := by
    simpa only [Function.comp_def] using roundCoordDensity_smooth.mul
      ((ContinuousLinearMap.contDiff L).comp ((hdc p).comp seedCoordEquiv.contDiff))
  rw [← partialJet_sub _ _ hbs hds,hsub]
  exact (partialJet_norm_le_iterated _ (roundCoordDensity_smooth.mul hF) ds x).trans
    (hmult.trans_eq (by dsimp [D] <;> ring))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereCoefficientDivergenceJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Metric
open scoped ContDiff
noncomputable section

theorem sphere_coefficient_divergence_jet_bound (J : ℕ) :
    ∃ C > 0, ∀ (P : Finset Base) (d b : SphereEnergyData),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density → ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
        (∀ i j, |partialJet (fun y ↦ sphereChartPrincipalDensity b p y i j) ds x-
          partialJet (fun y ↦ sphereChartPrincipalDensity d p y i j) ds x| ≤
            C*sphereCoefficientDistance P J d.tensor d.density b.tensor b.density) ∧
        |partialJet (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) ds x-
          partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x| ≤
            C*sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  choose K hK hKb using (fun i j : Fin 4 ↦ sphere_weighted_coefficient_scalar_jet_bound J (coefficientPrincipalEntry i j))
  obtain ⟨R,hR,hRb⟩ := sphere_weighted_coefficient_scalar_jet_bound J
    (ContinuousLinearMap.snd ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) ℝ)
  let C := R+∑ i, ∑ j, K i j
  have hsum : 0 ≤ ∑ i, ∑ j, K i j := Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ (hK i j).le))
  have hRC : R ≤ C := by dsimp [C] <;> linarith
  have hKC (i j : Fin 4) : K i j ≤ C := by
    have h1 := Finset.single_le_sum (fun j _ ↦ (hK i j).le) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (s := Finset.univ)
      (fun j _ ↦ (hK i j).le)) (Finset.mem_univ i)
    dsimp [C]
    linarith
  refine ⟨C,hR.trans_le hRC,?_⟩
  intro P d b hd hb p hp x hx ds hds
  have hD := sphereCoefficientDistance_nonneg P J d.tensor b.tensor d.density b.density
    (fun q _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q)
    (fun q _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q)
  constructor
  · intro i j
    have h := hKb i j P d b hd hb p hp x hx ds hds
    simp only [coefficientPrincipalEntry_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hKC i j) hD)
  · have h := hRb P d b hd hb p hp x hx ds hds
    exact h.trans (mul_le_mul_of_nonneg_right hRC hD)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFinitePositiveBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau

theorem real_finite_positive_majorant {ι : Type*} [Fintype ι] (C : ι → ℝ) :
    ∃ B > 0, ∀ i, C i ≤ B := by
  classical
  refine ⟨(∑ i, |C i|)+1,by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ abs_nonneg (C i))],?_⟩
  intro i
  have hs := Finset.single_le_sum (f := fun j ↦ |C j|) (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)
  linarith [le_abs_self (C i)]

end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereForcingJetNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis Metric
open scoped ContDiff
noncomputable section

theorem sphere_weighted_density_finite_jet_bound (P : Finset Base) (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (J : ℕ) :
    ∃ B > 0, ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
        |partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x| ≤ B := by
  have hr (p : Base) : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) :=
    roundCoordDensity_smooth.mul (spherePullback_smooth d.density hd p)
  choose C hC hCb using (fun p : P ↦ compact_real_derivative_bound _ (hr p)
    (isCompact_closedBall (0 : Yau.Jets.Coord) 1) J)
  obtain ⟨B,hB,hmajor⟩ := Yau.real_finite_positive_majorant C
  refine ⟨B,hB,?_⟩
  intro p hp x hx ds hds
  exact (partialJet_norm_le_iterated _ (hr p) ds x).trans
    ((hCb ⟨p,hp⟩ ds.length hds x hx).trans (hmajor ⟨p,hp⟩))

theorem sphere_finite_norm_divergence_neighborhood (P : Finset Base) (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (lam₀ : ℝ) (J : ℕ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta > 0, ∀ (b : SphereEnergyData) (lam : ℝ),
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density < eta →
      |lam-lam₀| < eta →
      ∀ p ∈ P, ∀ x ∈ closedBall (0 : Yau.Jets.Coord) 1,
      ∀ ds : List (Fin 4), ds.length ≤ J →
        (∀ i j, |partialJet (fun y ↦ sphereChartPrincipalDensity b p y i j) ds x-
          partialJet (fun y ↦ sphereChartPrincipalDensity d p y i j) ds x| ≤ eps) ∧
        |partialJet (fun y ↦ lam*(roundCoordDensity y*b.density (sphereChartCoordMap p y))) ds x-
          partialJet (fun y ↦ lam₀*(roundCoordDensity y*d.density (sphereChartCoordMap p y))) ds x| ≤ eps ∧
        |partialJet (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) ds x-
          partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x| ≤ eps := by
  obtain ⟨C,hC,hCb⟩ := sphere_coefficient_divergence_jet_bound J
  obtain ⟨B,hB,hBb⟩ := sphere_weighted_density_finite_jet_bound P d hd J
  let K := C+(|lam₀|+1)*C+B+1
  have hK : 0 < K := by dsimp [K] <;> positivity
  let eta := min 1 (eps/K)
  have heta : 0 < eta := lt_min zero_lt_one (div_pos heps hK)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hbudget : K*eta ≤ eps := by
    have h : eta ≤ eps/K := min_le_right _ _
    nlinarith [(le_div_iff₀ hK).mp h]
  refine ⟨eta,heta,?_⟩
  intro b lam hb hdist hlam p hp x hx ds hds
  let D := sphereCoefficientDistance P J d.tensor d.density b.tensor b.density
  have hD : 0 ≤ D := sphereCoefficientDistance_nonneg P J d.tensor b.tensor d.density b.density
    (fun q _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q)
    (fun q _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q)
  have hCD : C*D ≤ eps := by
    have hCK : C ≤ K := by
      dsimp [K]
      nlinarith [mul_nonneg (show 0 ≤ |lam₀|+1 by positivity) hC.le]
    exact (mul_le_mul_of_nonneg_left hdist.le hC.le).trans
      ((mul_le_mul_of_nonneg_right hCK heta.le).trans hbudget)
  obtain ⟨hprincipal,hrho⟩ := hCb P d b hd hb p hp x hx ds hds
  refine ⟨fun i j ↦ (hprincipal i j).trans hCD,?_,hrho.trans hCD⟩
  have hbd : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) :=
    roundCoordDensity_smooth.mul (spherePullback_smooth b.density hb p)
  have hdd : ContDiff ℝ ∞ (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) :=
    roundCoordDensity_smooth.mul (spherePullback_smooth d.density hd p)
  rw [partialJet_const_mul _ hbd,partialJet_const_mul _ hdd]
  let rb := partialJet (fun y ↦ roundCoordDensity y*b.density (sphereChartCoordMap p y)) ds x
  let rd := partialJet (fun y ↦ roundCoordDensity y*d.density (sphereChartCoordMap p y)) ds x
  have hrd : |rd| ≤ B := hBb p hp x hx ds hds
  have hlamabs : |lam| ≤ |lam₀|+1 := by
    have hh : |lam| ≤ |lam-lam₀|+|lam₀| := by
      simpa only [sub_add_cancel] using abs_add_le (lam-lam₀) lam₀
    linarith [hlam.trans_le heta1]
  have hrb : |rb-rd| ≤ C*D := hrho
  change |lam*rb-lam₀*rd| ≤ eps
  calc
    _ = |lam*(rb-rd)+(lam-lam₀)*rd| := by congr 1; ring
    _ ≤ |lam| * |rb-rd|+|lam-lam₀| * |rd| := by simpa only [abs_mul] using abs_add_le (lam*(rb-rd)) ((lam-lam₀)*rd)
    _ ≤ (|lam₀|+1)*(C*D)+eta*B := add_le_add
      (mul_le_mul hlamabs hrb (abs_nonneg _) (by positivity))
      (mul_le_mul hlam.le hrd (abs_nonneg _) heta.le)
    _ ≤ (|lam₀|+1)*(C*eta)+eta*B := by gcongr
    _ ≤ K*eta := by dsimp [K] <;> nlinarith [mul_nonneg hC.le heta.le]
    _ ≤ eps := hbudget

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteLinearConstraints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
noncomputable section

theorem subspace_nonzero_linear_constraints {S : Type*} [AddCommGroup S] [Module ℝ S]
    {N : ℕ} (V : Submodule ℝ S) [FiniteDimensional ℝ V]
    (hV : N < Module.finrank ℝ V) (ell : Fin N → S →ₗ[ℝ] ℝ) :
    ∃ x : S, x ∈ V ∧ x ≠ 0 ∧ ∀ i, ell i x = 0 := by
  let L : V →ₗ[ℝ] (Fin N → ℝ) := LinearMap.pi (fun i ↦ (ell i).comp V.subtype)
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hV)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨x,x.property,fun h ↦ hx0 (Subtype.ext h),fun i ↦ congrFun (LinearMap.mem_ker.mp hx) i⟩

end
end Yau.Analysis

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

local instance sphereSmoothResolventBridgeMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothResolventBridgeBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereResolventFormBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section

local instance sphereFormBoundsMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereFormBoundsBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_resolvent_smooth_variational (d : SphereEnergyData)
    (mu : ℝ) (hmu : mu ≠ 0) (u : SphereEnergySmooth d)
    (he : sphereL2Resolvent d (sphereEnergyL2Linear d u) = mu • sphereEnergyL2Linear d u) :
    ∀ v : SphereEnergyHilbert d,
      inner ℝ (sphereEnergyToCompletion d u) v =
        mu⁻¹ * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v) := by
  have hz : sphereEnergyToCompletion d u = mu⁻¹ • sphereWeakSolution d (sphereEnergyL2Linear d u) := by
    apply sphereEnergyL2Map_injective d
    rw [sphereEnergyL2Map_coe,map_smul]
    change sphereEnergyL2Linear d u = mu⁻¹ • sphereL2Resolvent d (sphereEnergyL2Linear d u)
    rw [he,smul_smul,inv_mul_cancel₀ hmu,one_smul]
  intro v
  rw [hz,inner_smul_left_eq_smul,smul_eq_mul,sphereWeakSolution_spec]

theorem sphere_resolvent_quadratic_to_form_lower (d : SphereEnergyData)
    (mu : ℝ) (hmu : 0 < mu) (z : SphereEnergyHilbert d)
    (hz : sphereEnergyL2Map d z ≠ 0)
    (hb : inner ℝ (sphereL2Resolvent d (sphereEnergyL2Map d z)) (sphereEnergyL2Map d z) ≤
      mu * ‖sphereEnergyL2Map d z‖^2) :
    (mu⁻¹-1)*‖sphereEnergyL2Map d z‖^2 ≤ sphereCompletedDirichlet d z z := by
  let f := sphereEnergyL2Map d z
  have hweak : ‖sphereWeakSolution d f‖^2 ≤ mu*‖f‖^2 := by
    simpa only [sphereL2Resolvent_inner,real_inner_self_eq_norm_sq] using hb
  have hc := real_inner_le_norm (sphereWeakSolution d f) z
  rw [sphereWeakSolution_spec,real_inner_self_eq_norm_sq] at hc
  have hsq := mul_self_le_mul_self (sq_nonneg ‖f‖) hc
  have hprod := mul_le_mul_of_nonneg_right hweak (sq_nonneg ‖z‖)
  have hn : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hmain : ‖f‖^2 ≤ mu*‖z‖^2 := (mul_le_mul_iff_left₀ hn).mp (by nlinarith)
  have hdiv : ‖f‖^2 / mu ≤ ‖z‖^2 := (div_le_iff₀ hmu).mpr (by nlinarith [hmain])
  rw [sphereCompletedDirichlet,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  change (mu⁻¹-1)*‖f‖^2 ≤ ‖z‖^2-‖f‖^2
  rw [div_eq_mul_inv] at hdiv
  nlinarith

theorem sphere_smooth_rayleigh_of_resolvent_bound (d : SphereEnergyData)
    (mu : ℝ) (hmu : 0 < mu) (u : SphereEnergySmooth d) (hu : u ≠ 0)
    (hb : inner ℝ (sphereL2Resolvent d (sphereEnergyL2Linear d u)) (sphereEnergyL2Linear d u) ≤
      mu * ‖sphereEnergyL2Linear d u‖^2) :
    mu⁻¹-1 ≤ sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d u) := by
  have hn : sphereEnergyL2Linear d u ≠ 0 := fun h ↦ hu ((sphereEnergyL2Linear_eq_zero_iff d u).mp h)
  have h := sphere_resolvent_quadratic_to_form_lower d mu hmu (sphereEnergyToCompletion d u)
    (by simpa only [sphereEnergyL2Map_coe] using hn) (by simpa only [sphereEnergyL2Map_coe] using hb)
  rw [sphereEnergyL2Map_coe,sphereCompletedDirichlet_coe,sphereEnergyL2Linear_norm_sq] at h
  apply (le_div_iff₀ _).mpr h
  rw [← sphereEnergyL2Linear_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereSmoothFrameRayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Analysis
noncomputable section

local instance sphereFrameRayleighMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereFrameRayleighBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_smooth_frame_rayleigh_upper (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu) (x : SphereEnergySmooth d)
    (hx : x ∈ Submodule.span ℝ (range u)) (hx0 : x ≠ 0) :
    sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x) ≤
      (mu (Fin.last N))⁻¹-1 := by
  classical
  let J := sphereEnergyL2Linear d
  let C := sphereEnergyToCompletion d
  have hvar (i) (v : SphereEnergySmooth d) :
      inner ℝ (C (u i)) (C v) = (mu i)⁻¹ * inner ℝ (J (u i)) (J v) := by
    simpa only [C,J,sphereEnergyL2Map_coe] using
      sphere_resolvent_smooth_variational d (mu i) (hmu i).ne' (u i) (he i) (C v)
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hcoef (i) : inner ℝ (J (u i)) (J x) = c i := by
    rw [← hc,map_sum]
    simp only [map_smul]
    exact ho.inner_right_fintype c i
  have hnorm : ‖J x‖^2 = ∑ i, c i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [← hc]
    rw [map_sum]
    simp only [map_smul,sum_inner,inner_smul_left_eq_smul,smul_eq_mul,hcoef,pow_two]
  have henergy : ‖C x‖^2 = ∑ i, (mu i)⁻¹*c i^2 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rw 1 [← hc]
    rw [map_sum]
    simp only [map_smul,sum_inner,inner_smul_left_eq_smul,smul_eq_mul,hvar,hcoef]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : ‖C x‖^2 ≤ (mu (Fin.last N))⁻¹*‖J x‖^2 := by
    rw [hnorm,henergy,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (hmu (Fin.last N)) (hanti (Fin.le_last i)))
      (sq_nonneg (c i))
  have hpos : 0 < ‖J x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (fun h ↦ hx0 ((sphereEnergyL2Linear_eq_zero_iff d x).mp h)))
  have hd : sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d x) (SphereEnergySmooth.toSmooth d x) =
      ‖C x‖^2-‖J x‖^2 := by
    rw [← sphereCompletedDirichlet_coe,sphereCompletedDirichlet,sphereEnergyL2Map_coe,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  rw [sphereRayleighQuotient,hd,← sphereEnergyL2Linear_norm_sq]
  exact (div_le_iff₀ hpos).mpr (by nlinarith [hb])

theorem sphere_smooth_frame_rayleigh_minmax (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) :
    (∃ V : Submodule ℝ (SphereEnergySmooth d), FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
      ∀ x ∈ V, x ≠ 0 → sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x) ≤
        (mu (Fin.last N))⁻¹-1) ∧
    (∀ V : Submodule ℝ (SphereEnergySmooth d), FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : SphereEnergySmooth d, x ∈ V ∧ x ≠ 0 ∧
        (mu (Fin.last N))⁻¹-1 ≤ sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d x)) := by
  constructor
  · refine ⟨Submodule.span ℝ (range u),FiniteDimensional.span_of_finite ℝ (finite_range u),?_,?_⟩
    · have hli : LinearIndependent ℝ u := LinearIndependent.of_comp (sphereEnergyL2Linear d) ho.linearIndependent
      simpa using finrank_span_eq_card hli
    · exact sphere_smooth_frame_rayleigh_upper d u mu ho hmu he hanti
  · intro V hV hdim
    let := hV
    obtain ⟨x,hx,hx0,horth⟩ := subspace_nonzero_linear_constraints V (by omega)
      (fun i : Fin N ↦ (innerSL ℝ (sphereEnergyL2Linear d (u i.castSucc))).toLinearMap.comp (sphereEnergyL2Linear d))
    refine ⟨x,hx,hx0,sphere_smooth_rayleigh_of_resolvent_bound d _ (hmu _) x hx0 ?_⟩
    apply hmax
    intro j hj
    exact horth ⟨j.val,hj⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereIndexedRayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set
open scoped ContDiff
noncomputable section

local instance sphereIndexedRayleighMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedRayleighBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_rayleigh_levels_nonneg (d : SphereEnergyData) (N : ℕ)
    (a : ℝ) (ha : a ∈ sphereRayleighUpperLevels d N) : 0 ≤ a := by
  obtain ⟨V,hV,hdim,hbound⟩ := ha
  let := hV
  have hV0 : V ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
  apply le_trans _ (hbound x hx hx0)
  apply div_nonneg (sphereDirichletForm_nonneg d.tensor d.pos x)
  exact (sphereWeightedPairing_self_pos d.density x d.continuous d.positive x.property.continuous
    (fun h ↦ hx0 (Subtype.ext h))).le

theorem sphereIndexedEigenvalue_eq_of_minmax (d : SphereEnergyData) (N : ℕ) (a : ℝ)
    (hupper : a ∈ sphereRayleighUpperLevels d N)
    (hlower : ∀ V : Submodule ℝ sphereSmoothFunctions,
      FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : sphereSmoothFunctions, x ∈ V ∧ x ≠ 0 ∧ a ≤ sphereRayleighQuotient d.tensor d.density x) :
    sphereIndexedEigenvalue d N = a := by
  have hbelow : ∀ b ∈ sphereRayleighUpperLevels d N, a ≤ b := by
    rintro b ⟨V,hV,hdim,hb⟩
    obtain ⟨x,hx,hx0,hlo⟩ := hlower V hV hdim
    exact hlo.trans (hb x hx hx0)
  exact le_antisymm (csInf_le ⟨a,hbelow⟩ hupper) (le_csInf ⟨a,hupper⟩ hbelow)

theorem sphereIndexedEigenvalue_eq_frame (d : SphereEnergyData) {N : ℕ}
    (u : Fin (N+1) → SphereEnergySmooth d) (mu : Fin (N+1) → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) :
    sphereIndexedEigenvalue d N = (mu (Fin.last N))⁻¹-1 := by
  obtain ⟨hup,hlo⟩ := sphere_smooth_frame_rayleigh_minmax d u mu ho hmu he hanti hmax
  exact sphereIndexedEigenvalue_eq_of_minmax d N _ hup hlo

theorem sphereIndexedEigenvalue_minmax (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    sphereIndexedEigenvalue d N ∈ sphereRayleighUpperLevels d N ∧
    (∀ V : Submodule ℝ sphereSmoothFunctions, FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
      ∃ x : sphereSmoothFunctions, x ∈ V ∧ x ≠ 0 ∧
        sphereIndexedEigenvalue d N ≤ sphereRayleighQuotient d.tensor d.density x) ∧
    0 ≤ sphereIndexedEigenvalue d N := by
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  obtain ⟨hup,hlo⟩ := sphere_smooth_frame_rayleigh_minmax d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  have hupp : sphereIndexedEigenvalue d N ∈ sphereRayleighUpperLevels d N := heq.symm ▸ hup
  exact ⟨hupp,heq.symm ▸ hlo,sphere_rayleigh_levels_nonneg d N _ hupp⟩

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

theorem sphereCoefficientDistance_density_bound (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x)
    (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (J : ℕ) (x : Base) :
    |b.density x-d.density x| ≤ sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  obtain ⟨p,hp,z,hz,rfl⟩ := hcover x
  exact (norm_snd_le (intrinsicChartCoefficient b.tensor b.density p z-
    intrinsicChartCoefficient d.tensor d.density p z)).trans
    (sphereCoefficientDistance_value_bound P J d.tensor b.tensor d.density b.density
      (fun q _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q)
      (fun q _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q)
      p hp z hz)

theorem sphere_finite_norm_density_uniform_convergence (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x)
    (d : SphereEnergyData) (b : ℕ → SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) (J : ℕ)
    (ht : Tendsto (fun j ↦ sphereCoefficientDistance P J d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    TendstoUniformly (fun j ↦ (b j).density) d.density atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with j hj x
  simpa only [Real.dist_eq,abs_sub_comm] using
    (sphereCoefficientDistance_density_bound P hcover d (b j) hd (hb j) J x).trans_lt hj

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereFiniteNormIndexedCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Yau.Geometry Yau.Analysis Metric Filter
open scoped ContDiff Topology
noncomputable section

local instance sphereFiniteNormCompactMeasurable_rc3cc3b_1 : MeasurableSpace Base := borel Base
local instance sphereFiniteNormCompactBorel_rc3cc3b_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_finite_norm_indexed_compactness_oai (d₀ : SphereEnergyData)
    (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density) (N n : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) (1/512), sphereChartCoordMap p z=x) ∧
      ∃ eta > 0, ∀ b : ℕ → SphereEnergyData,
        (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density) →
        (∀ j, sphereCoefficientDistance P (n+6) d₀.tensor d₀.density (b j).tensor (b j).density < eta) →
        ∀ f : ∀ j, SphereWeightedL2 (b j),
          (∀ j, sphereL2Resolvent (b j) (f j)=(sphereIndexedEigenvalue (b j) N+1)⁻¹ • f j) →
          (∀ j, ‖f j‖=1) →
          ∃ u : ℕ → Base → ℝ,
            (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) ∧
            (∀ j, u j =ᵐ[sphereWeightedMeasure (b j).density] (f j : Base → ℝ)) ∧
            (∀ j, sphereWeightedPairing (b j).density (u j) (u j)=1) ∧
            (∀ j, u j ≠ 0) ∧
            ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
              ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
                (∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
                  TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) ds)
                    (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 (1/256))) ∧
                (Tendsto (fun j ↦ sphereCoefficientDistance P (n+6) d₀.tensor d₀.density
                    (b j).tensor (b j).density) atTop (𝓝 0) →
                  sphereWeightedPairing d₀.density v v=1 ∧ v ≠ 0) := by
  have hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)) :=
    fun p ↦ (hd₀.comp (sphereChartCoordMap_smooth p)).contDiff
  obtain ⟨P,hP,eps,heps,H⟩ := sphere_eigen_global_neighborhood_compactness d₀ hrho₀
    (sphereIndexedEigenvalue d₀ N+1)⁻¹ n
  have hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z=x := by
    intro x
    obtain ⟨p,hp,z,hz,hzx⟩ := hP x
    exact ⟨p,hp,seedCoordEquiv z,⟨z,(closedBall_subset_closedBall (by norm_num : (1:ℝ)/512 ≤ 1))
      (ball_subset_closedBall hz),rfl⟩,hzx⟩
  obtain ⟨eta₀,h₀,H₀⟩ := sphere_finite_norm_divergence_neighborhood P d₀ hd₀
    (sphereIndexedEigenvalue d₀ N) (n+6) eps heps
  obtain ⟨eta₁,h₁,H₁⟩ := sphere_finite_norm_indexed_eigenvalue_continuity P hcover d₀ hd₀ N eta₀ h₀
  refine ⟨P,hP,min eta₀ eta₁,lt_min h₀ h₁,?_⟩
  intro b hb hdist f heigen hn
  have hrho (j : ℕ) (p : Base) : ContDiff ℝ ∞ (fun x ↦ (b j).density (sphereChartCoordMap p x)) :=
    ((hb j).comp (sphereChartCoordMap_smooth p)).contDiff
  have hmu (j : ℕ) : (sphereIndexedEigenvalue (b j) N+1)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    have hp := (sphereIndexedEigenvalue_minmax (b j) (hrho j) N).2.2
    linarith
  have hclose (j : ℕ) := H₀ (b j) (sphereIndexedEigenvalue (b j) N) (hb j)
    ((hdist j).trans_le (min_le_left _ _))
    (H₁ (b j) (hb j) ((sphereCoefficientDistance_mono_order P d₀ (b j) hd₀ (hb j) 0 (n+6) (by omega)).trans_lt
      ((hdist j).trans_le (min_le_right _ _))))
  have hchart := H b (fun j ↦ (sphereIndexedEigenvalue (b j) N+1)⁻¹) hrho hmu
    (fun j p hp x hx ds hds ↦ by
      have h := hclose j p hp x ((closedBall_subset_closedBall (by norm_num : (1:ℝ)/128 ≤ 1)) hx) ds hds
      refine ⟨h.1,?_⟩
      change |partialJet (fun y ↦ (((sphereIndexedEigenvalue (b j) N+1)⁻¹)⁻¹-1) *
        (roundCoordDensity y*(b j).density (sphereChartCoordMap p y))) ds x-
        partialJet (fun y ↦ (((sphereIndexedEigenvalue d₀ N+1)⁻¹)⁻¹-1) *
          (roundCoordDensity y*d₀.density (sphereChartCoordMap p y))) ds x| ≤ eps
      simpa only [inv_inv,add_sub_cancel_right] using h.2.1)
    (fun j p hp x hx ↦ (hclose j p hp x
      ((closedBall_subset_closedBall (by norm_num : (1:ℝ)/128 ≤ 1)) hx) [] (by simp)).2.2)
    f heigen hn
  obtain ⟨u,hu,ha,huN,hu0,v,hv,nu,hnu,ht,hjet,hnorm⟩ := hchart
  refine ⟨u,hu,ha,huN,hu0,v,hv,nu,hnu,ht,hjet,?_⟩
  intro hlim
  exact hnorm (sphere_finite_norm_density_uniform_convergence P hcover d₀ b hd₀ hb (n+6) hlim)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_finite_norm_indexed_compactness_oai := @OAI.Yau.Target.sphere_finite_norm_indexed_compactness_oai
