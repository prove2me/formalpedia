-- Prove2me | solution 1 for OAI.Yau.Target.sphere_finite_norm_indexed_eigenvalue_continuity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:52.84464+00:00
-- url     : https://prove2.me/submissions/1c8428d4-1a9a-4097-82ed-04970284403f

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

local instance sphereEnergyL2MapMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2MapBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereWeightedL1BoundMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereWeightedL1BoundBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereSmoothGreenBoundMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothGreenBoundBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereWeakResolventMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereWeakResolventBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereEnergyL2InjectiveMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereEnergyL2InjectiveBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereSmoothResolventBridgeMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereSmoothResolventBridgeBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereFormBoundsMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereFormBoundsBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereFrameRayleighMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereFrameRayleighBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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

local instance sphereIndexedRayleighMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedRayleighBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereIntegratedFormComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory
open scoped ContDiff
noncomputable section

theorem sphere_integrated_form_comparison
    (A B : IntrinsicTensor) (hA : IntrinsicTensorSmooth A) (hB : IntrinsicTensorSmooth B)
    (hAs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hBs : ∀ x alpha beta, B x alpha beta = B x beta alpha)
    (hAp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (hBp : ∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha)
    (rho sigma : Base → ℝ) (hr : Continuous rho) (hsig : Continuous sigma)
    (eps : ℝ)
    (hcomp : ∀ x : Base, (∀ alpha : SphereCotangent x,
      |B x alpha alpha-A x alpha alpha| ≤ eps*A x alpha alpha) ∧
      |sigma x-rho x| ≤ eps*rho x)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) :
    (1-eps)*sphereDirichletForm A u u ≤ sphereDirichletForm B u u ∧
    sphereDirichletForm B u u ≤ (1+eps)*sphereDirichletForm A u u ∧
    (1-eps)*sphereWeightedPairing rho u u ≤ sphereWeightedPairing sigma u u ∧
    sphereWeightedPairing sigma u u ≤ (1+eps)*sphereWeightedPairing rho u u := by
  have hIA := intrinsic_differential_pair_integrable A hA hAs hAp u u hu hu
  have hIB := intrinsic_differential_pair_integrable B hB hBs hBp u u hu hu
  have hIr := sphereWeightedPairing_integrable rho u u hr hu.continuous hu.continuous
  have hIs := sphereWeightedPairing_integrable sigma u u hsig hu.continuous hu.continuous
  have hE (x : Base) := abs_le.mp ((hcomp x).1 (sphereDifferential u x))
  have hD (x : Base) :
      (1-eps)*(rho x*u x*u x) ≤ sigma x*u x*u x ∧
      sigma x*u x*u x ≤ (1+eps)*(rho x*u x*u x) := by
    have hh := abs_le.mp (hcomp x).2
    have hlo := mul_le_mul_of_nonneg_right hh.1 (sq_nonneg (u x))
    have hhi := mul_le_mul_of_nonneg_right hh.2 (sq_nonneg (u x))
    constructor <;> nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold sphereDirichletForm
    rw [← integral_const_mul]
    exact integral_mono (hIA.const_mul (1-eps)) hIB (fun x ↦ by nlinarith [hE x])
  · unfold sphereDirichletForm
    rw [← integral_const_mul]
    exact integral_mono hIB (hIA.const_mul (1+eps)) (fun x ↦ by nlinarith [hE x])
  · unfold sphereWeightedPairing
    rw [← integral_const_mul]
    exact integral_mono (hIr.const_mul (1-eps)) hIs (fun x ↦ (hD x).1)
  · unfold sphereWeightedPairing
    rw [← integral_const_mul]
    exact integral_mono hIs (hIr.const_mul (1+eps)) (fun x ↦ (hD x).2)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_SphereRayleighComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff
noncomputable section

lemma positive_ratio_relative_bounds {E F D G eps : ℝ}
    (hE : 0 ≤ E) (hD : 0 < D) (hG : 0 < G) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hlo : (1-eps)*E ≤ F) (hhi : F ≤ (1+eps)*E)
    (hdlo : (1-eps)*D ≤ G) (hdhi : G ≤ (1+eps)*D) :
    (1-eps)/(1+eps)*(E/D) ≤ F/G ∧ F/G ≤ (1+eps)/(1-eps)*(E/D) := by
  constructor
  · calc
      _ = ((1-eps)*E)/((1+eps)*D) := div_mul_div_comm _ _ _ _
      _ ≤ ((1-eps)*E)/G := div_le_div_of_nonneg_left
        (mul_nonneg (by linarith) hE) hG hdhi
      _ ≤ F/G := div_le_div_of_nonneg_right hlo hG.le
  · calc
      _ ≤ ((1+eps)*E)/G := div_le_div_of_nonneg_right hhi hG.le
      _ ≤ ((1+eps)*E)/((1-eps)*D) := div_le_div_of_nonneg_left
        (mul_nonneg (by linarith) hE) (mul_pos (by linarith) hD) hdlo
      _ = _ := (div_mul_div_comm _ _ _ _).symm

theorem sphere_finite_norm_rayleigh_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hAs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hAp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ eta > 0, ∀ (B : IntrinsicTensor) (sigma : Base → ℝ),
      IntrinsicTensorSmooth B → (∀ x alpha beta, B x alpha beta = B x beta alpha) →
      (∀ x alpha, alpha ≠ 0 → 0 < B x alpha alpha) →
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ sigma → (∀ x, 0 < sigma x) →
      sphereCoefficientDistance P 0 A rho B sigma < eta →
      ∀ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → u ≠ 0 →
        (1-eps)/(1+eps)*sphereRayleighQuotient A rho u ≤ sphereRayleighQuotient B sigma u ∧
        sphereRayleighQuotient B sigma u ≤ (1+eps)/(1-eps)*sphereRayleighQuotient A rho u := by
  obtain ⟨eta,heta,hcomp⟩ := sphere_coefficient_relative_form_comparison P hcover A hA hAs hAp rho hr hrp eps heps
  refine ⟨eta,heta,?_⟩
  intro B sigma hB hBs hBp hsig hsigp hdist u hu hune
  obtain ⟨hlo,hhi,hdlo,hdhi⟩ := sphere_integrated_form_comparison A B hA hB hAs hBs hAp hBp
    rho sigma hr.continuous hsig.continuous eps (hcomp B sigma hB hBs hBp hsig hdist) u hu
  exact positive_ratio_relative_bounds (sphereDirichletForm_nonneg A hAp u)
    (sphereWeightedPairing_self_pos rho u hr.continuous hrp hu.continuous hune)
    (sphereWeightedPairing_self_pos sigma u hsig.continuous hsigp hu.continuous hune)
    heps.le heps1 hlo hhi hdlo hdhi

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SphereIndexedCoefficientComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section

local instance sphereIndexedComparisonMeasurable_re33ac8_1 : MeasurableSpace Base := borel Base
local instance sphereIndexedComparisonBorel_re33ac8_1 : BorelSpace Base := ⟨rfl⟩
theorem sphereIndexedEigenvalue_le_of_rayleigh (d b : SphereEnergyData)
    (hd : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (hb : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ b.density (sphereChartCoordMap p x)))
    (c : ℝ) (hc : 0 ≤ c)
    (hcomp : ∀ u : sphereSmoothFunctions, u ≠ 0 →
      sphereRayleighQuotient b.tensor b.density u ≤ c*sphereRayleighQuotient d.tensor d.density u)
    (N : ℕ) : sphereIndexedEigenvalue b N ≤ c*sphereIndexedEigenvalue d N := by
  obtain ⟨V,hV,hdim,hVbound⟩ := (sphereIndexedEigenvalue_minmax d hd N).1
  obtain ⟨x,hx,hx0,hxlo⟩ := (sphereIndexedEigenvalue_minmax b hb N).2.1 V hV hdim
  exact hxlo.trans ((hcomp x hx0).trans (mul_le_mul_of_nonneg_left (hVbound x hx hx0) hc))

theorem sphereIndexedEigenvalue_ge_of_rayleigh (d b : SphereEnergyData)
    (hd : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (hb : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ b.density (sphereChartCoordMap p x)))
    (c : ℝ) (hc : 0 ≤ c)
    (hcomp : ∀ u : sphereSmoothFunctions, u ≠ 0 →
      c*sphereRayleighQuotient d.tensor d.density u ≤ sphereRayleighQuotient b.tensor b.density u)
    (N : ℕ) : c*sphereIndexedEigenvalue d N ≤ sphereIndexedEigenvalue b N := by
  obtain ⟨V,hV,hdim,hVbound⟩ := (sphereIndexedEigenvalue_minmax b hb N).1
  obtain ⟨x,hx,hx0,hxlo⟩ := (sphereIndexedEigenvalue_minmax d hd N).2.1 V hV hdim
  exact (mul_le_mul_of_nonneg_left hxlo hc).trans ((hcomp x hx0).trans (hVbound x hx hx0))

theorem sphere_finite_norm_indexed_eigenvalue_comparison (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ eta > 0, ∀ b : SphereEnergyData,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
      ∀ N : ℕ,
        (1-eps)/(1+eps)*sphereIndexedEigenvalue d N ≤ sphereIndexedEigenvalue b N ∧
        sphereIndexedEigenvalue b N ≤ (1+eps)/(1-eps)*sphereIndexedEigenvalue d N := by
  obtain ⟨eta,heta,hcomp⟩ := sphere_finite_norm_rayleigh_comparison P hcover
    d.tensor d.smooth d.symm d.pos d.density hd d.positive eps heps heps1
  refine ⟨eta,heta,?_⟩
  intro b hb hdist N
  have hdloc (p) := (hd.comp (sphereChartCoordMap_smooth p)).contDiff
  have hbloc (p) := (hb.comp (sphereChartCoordMap_smooth p)).contDiff
  have hc (u : sphereSmoothFunctions) (hu : u ≠ 0) := hcomp b.tensor b.density
    b.smooth b.symm b.pos hb b.positive hdist u u.property (fun h ↦ hu (Subtype.ext h))
  constructor
  · exact sphereIndexedEigenvalue_ge_of_rayleigh d b hdloc hbloc _
      (div_nonneg (by linarith) (by linarith)) (fun u hu ↦ (hc u hu).1) N
  · exact sphereIndexedEigenvalue_le_of_rayleigh d b hdloc hbloc _
      (div_nonneg (by linarith) (by linarith)) (fun u hu ↦ (hc u hu).2) N

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereIndexedContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem relative_comparison_absolute_neighborhood (a : ℝ) (ha : 0 ≤ a)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps > 0, eps < 1 ∧ ∀ b : ℝ,
      (1-eps)/(1+eps)*a ≤ b → b ≤ (1+eps)/(1-eps)*a → |b-a| < delta := by
  have hden : 0 < 2*a+delta+1 := by linarith
  obtain ⟨eps,heps,hepslt⟩ := exists_between
    (lt_min (by norm_num : (0:ℝ)<1/2) (div_pos hdelta hden))
  have hepshalf : eps < 1/2 := hepslt.trans_le (min_le_left _ _)
  have hsmall : eps*(2*a+delta+1) < delta := (lt_div_iff₀ hden).mp
    (hepslt.trans_le (min_le_right _ _))
  have hm : 0 < 1-eps := by linarith
  have hp : 0 < 1+eps := by linarith
  refine ⟨eps,heps,by linarith,?_⟩
  intro b hlo hhi
  rw [div_mul_eq_mul_div] at hlo hhi
  have hlo' := (div_le_iff₀ hp).mp hlo
  have hhi' := (le_div_iff₀ hm).mp hhi
  apply abs_lt.mpr
  constructor
  · by_contra h
    have hb : b ≤ a-delta := by linarith
    have hprod := mul_le_mul_of_nonneg_right hb hp.le
    nlinarith
  · by_contra h
    have hb : a+delta ≤ b := by linarith
    have hprod := mul_le_mul_of_nonneg_right hb hm.le
    nlinarith

theorem sphere_finite_norm_indexed_eigenvalue_continuity_oai (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm z = x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (N : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eta > 0, ∀ b : SphereEnergyData,
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
      sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
      |sphereIndexedEigenvalue b N-sphereIndexedEigenvalue d N| < delta := by
  have hnonneg := (sphereIndexedEigenvalue_minmax d
    (fun p ↦ (hd.comp (sphereChartCoordMap_smooth p)).contDiff) N).2.2
  obtain ⟨eps,heps,heps1,habs⟩ := relative_comparison_absolute_neighborhood
    (sphereIndexedEigenvalue d N) hnonneg delta hdelta
  obtain ⟨eta,heta,hcomp⟩ := sphere_finite_norm_indexed_eigenvalue_comparison P hcover d hd eps heps heps1
  exact ⟨eta,heta,fun b hb hdist ↦ habs _ (hcomp b hb hdist N).1 (hcomp b hb hdist N).2⟩

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_finite_norm_indexed_eigenvalue_continuity_oai := @OAI.Yau.Target.sphere_finite_norm_indexed_eigenvalue_continuity_oai
