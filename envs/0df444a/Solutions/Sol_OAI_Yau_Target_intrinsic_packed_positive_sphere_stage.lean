-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_packed_positive_sphere_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:33:10.368768+00:00
-- url     : https://prove2.me/submissions/f8bde6b5-1fa9-4ab8-906a-60287538aa59

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
import Theorems.Thm_OAI_Yau_Target_corrected_exterior_equation
import Theorems.Thm_OAI_Yau_Target_intrinsic_packed_small_corrected_stage

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ManifoldCompactExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M] [LocallyCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma manifold_compact_smooth_cutoff {K U : Set M} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ U ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      ∀ x ∈ K, b =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hb1,hb0,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    I hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hsupp : tsupport (b : M → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra h
    exact hx (hb0 x h)
  refine ⟨b,b.contMDiff,hL.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans hLU,hb,?_⟩
  intro x hx
  exact Filter.Eventually.filter_mono (nhds_le_nhdsSet hx) hb1

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r356339_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

lemma ambientComplexSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientComplexSeed N) :=
  seedQuadratic_contDiff.pow N

lemma ambientRealSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientRealSeed N) :=
  Complex.reCLM.contDiff.comp (ambientComplexSeed_contDiff N)

lemma sphericalSeed_smooth (N : ℕ) : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (sphericalSeed N) :=
  (ambientRealSeed_contDiff N).contMDiff.comp (contMDiff_coe_sphere (n := 4))

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordinateField
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section

lemma seedCoordinateField_smooth (N : ℕ) : ContDiff ℝ ∞ (seedCoordinateField N) :=
  (ambientRealSeed_contDiff N).comp (seedChartAmbient_smooth.comp seedCoordEquiv.contDiff)

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

lemma seedSphereFromCoord_to {p : Base} (hp : p ∈ (extChartAt (𝓡 4) seedPoint).source) :
    seedSphereFromCoord (seedSphereToCoord p) = p := by
  unfold seedSphereToCoord seedSphereFromCoord
  rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv hp]

theorem seed_chart_scalar_extension (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport v) :
    ∃ F : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F ∧
      tsupport F ⊆ seedSphereFromCoord '' tsupport v ∧
      ∀ x, F (seedSphereFromCoord x) = v x := by
  let K := seedSphereFromCoord '' tsupport v
  have hK : IsCompact K := hc.image seedSphereFromCoord_continuous
  have hKU : K ⊆ (extChartAt (𝓡 4) seedPoint).source := by
    rintro p ⟨x,hx,rfl⟩
    exact seedSphereFromCoord_source x
  have hU : IsOpen (extChartAt (𝓡 4) seedPoint).source := isOpen_extChartAt_source seedPoint
  obtain ⟨b,hb,hbc,hbs,hbr,hb1⟩ := manifold_compact_smooth_cutoff (I := 𝓡 4) hK hU hKU
  let F : Base → ℝ := fun p ↦ b p*v (seedSphereToCoord p)
  have hF : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ F := by
    intro p
    by_cases hp : p ∈ tsupport b
    · have hcoord : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) ∞ seedSphereToCoord p :=
        seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp p
          (contMDiffAt_extChartAt' (by simpa using hbs hp))
      exact (hb p).mul (hv.contMDiff.contMDiffAt.comp p hcoord)
    · apply (contMDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with z hz
      simp [F,hz]
  have hs : tsupport F ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    have hbne : b p ≠ 0 := fun h ↦ hp (by simp [F,h])
    have hvne : v (seedSphereToCoord p) ≠ 0 := fun h ↦ hp (by simp [F,h])
    exact ⟨seedSphereToCoord p,subset_closure hvne,
      seedSphereFromCoord_to (hbs (subset_closure hbne))⟩
  refine ⟨F,hF,hs,?_⟩
  intro x
  dsimp [F]
  rw [seedSphereToCoord_from]
  by_cases hx : v x = 0
  · simp [hx]
  · have h := (hb1 (seedSphereFromCoord x) ⟨x,subset_closure hx,rfl⟩).eq_of_nhds
    rw [h,one_mul]

theorem seed_plus_compact_sphere_field (v : Yau.Jets.Coord → ℝ)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) (n : ℕ) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
      tsupport (u-sphericalSeed n) ⊆ seedSphereFromCoord '' tsupport v ∧
      ∀ x, u (seedSphereFromCoord x) = seedCoordinateField n x+v x := by
  obtain ⟨F,hF,hFs,hval⟩ := seed_chart_scalar_extension v hv hc
  refine ⟨sphericalSeed n+F,(sphericalSeed_smooth n).add hF,?_,?_⟩
  · simpa using hFs
  · intro x
    change sphericalSeed n (seedSphereFromCoord x)+F (seedSphereFromCoord x) = _
    rw [hval]
    rfl

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
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
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

attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst7
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst8
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst9
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst10
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst11
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst2
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst4
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst1
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst3
local instance positiveSphereCorrectionLocalInst5_r356339_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst6_r356339_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst12_r356339_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst13
local instance positiveSphereCorrectionLocalInst14_r356339_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst15
attribute [local instance] OAI.Yau.Target.positiveSphereCorrectionLocalInst16
lemma seed_scalar_extension_bound (v : Yau.Jets.Coord → ℝ) (V : Base → ℝ)
    (hs : tsupport V ⊆ seedSphereFromCoord '' tsupport v)
    (he : ∀ x, V (seedSphereFromCoord x) = v x) {eps : ℝ} (hp : 0 ≤ eps)
    (hb : ∀ x, |v x| ≤ eps) : ∀ p, |V p| ≤ eps := by
  intro p
  by_cases h : p ∈ tsupport V
  · obtain ⟨x,_,rfl⟩ := hs h
    rw [he]
    exact hb x
  · rw [image_eq_zero_of_notMem_tsupport h,abs_zero]
    exact hp

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

theorem positive_sphere_scalar_correction (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, ∀ (alpha beta : Yau.Jets.Coord → ℝ) (Q : Set Yau.Jets.Coord),
      IsCompact Q → ContDiff ℝ ∞ alpha → ContDiff ℝ ∞ beta →
      tsupport alpha ⊆ Q → tsupport beta ⊆ Q → ∀ eps : ℝ, 0 ≤ eps → eps < c →
      (∀ x, |alpha x| ≤ eps) → (∀ x, |beta x| ≤ eps) →
      ∃ a b : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
        tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
        (∀ x, a (seedSphereFromCoord x) = alpha x) ∧
        (∀ x, b (seedSphereFromCoord x) = beta x) ∧
        (∀ x, |a x| ≤ eps) ∧ (∀ x, |b x| ≤ eps) ∧
        IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation a x) ∧
        (∀ x v w, (A x+roundTensorPerturbation a x) v w = (A x+roundTensorPerturbation a x) w v) ∧
        (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation a x) v v) ∧
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+b x) ∧
        ∀ x, 0 < rho x+b x := by
  obtain ⟨c,hc,hAm,hrm⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  refine ⟨c,hc,?_⟩
  intro alpha beta Q hQ has hbs haq hbq eps heps hec hab hbb
  obtain ⟨a,ha,hasup,haval⟩ := seed_chart_scalar_extension alpha has
    (hQ.of_isClosed_subset isClosed_closure haq)
  obtain ⟨b,hb,hbsup,hbval⟩ := seed_chart_scalar_extension beta hbs
    (hQ.of_isClosed_subset isClosed_closure hbq)
  have haB := seed_scalar_extension_bound alpha a hasup haval heps hab
  have hbB := seed_scalar_extension_bound beta b hbsup hbval heps hbb
  obtain ⟨hposA,hposR⟩ := round_perturbed_pair_positive A rho a b hc hAm hrm
    (fun x ↦ (haB x).trans_lt hec) (fun x ↦ (hbB x).trans_lt hec)
  refine ⟨a,b,ha,hb,hasup.trans (image_mono haq),hbsup.trans (image_mono hbq),haval,hbval,
    haB,hbB,hA.add_section (roundTensorPerturbation_smooth a ha),?_,hposA,hr.add hb,hposR⟩
  intro x v w
  change A x v w+a x*roundCotangentTensor x v w = A x w v+a x*roundCotangentTensor x w v
  rw [hs,roundCotangentTensor_symm]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteWaveSupport
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_tsupport_subset (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ)
    {C : Set _root_.OAI.Yau.Jets.Coord} (hC : IsClosed C) (hV : ∀ i, tsupport (V i) ⊆ C) :
    tsupport (gaussianWaveField V a) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  by_contra hxc
  apply hx
  have hz (i : ι) : V i x = 0 := image_eq_zero_of_notMem_tsupport (fun hi ↦ hxc (hV i hi))
  simp [gaussianWaveField,hz]

lemma complexified_tsupport_subset (u : _root_.OAI.Yau.Jets.Coord → ℝ) {C : Set _root_.OAI.Yau.Jets.Coord} (hC : IsClosed C)
    (hu : tsupport u ⊆ C) : tsupport (fun x ↦ (u x : ℂ)) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  apply hu
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

lemma source_residual_tsupport_subset
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (lam : ℂ) {C : Set _root_.OAI.Yau.Jets.Coord} (hC : IsClosed C) (hu : tsupport u ⊆ C) :
    tsupport (fun x ↦ sourceWeightedOperator g w u x + lam*u x) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  by_contra hxc
  have hz : x ∉ tsupport u := fun h ↦ hxc (hu h)
  have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hz
  have hop := (sourceOperator_eventuallyEq g w he).eq_of_nhds
  apply hx
  simp only [hop,sourceWeightedOperator_zero,Pi.zero_apply,he.eq_of_nhds,mul_zero,add_zero]

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma lattice_scale_pos {n : ℕ} (hn : 0 < n) : 0 < (n:ℝ)^(-1/2:ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem finite_source_grid {U : Set _root_.OAI.Yau.Jets.Coord} (hU : Bornology.IsBounded U)
    {n : ℕ} (hn : 0 < n) : Finite (SourceGrid U n) := by
  obtain ⟨B,hB,hbound⟩ := hU.exists_pos_norm_le
  let r : ℝ := (n:ℝ)^(-1/2:ℝ)
  have hr : 0 < r := lattice_scale_pos hn
  let M : ℤ := ⌈B/r⌉
  have hcoords (z : SourceGrid U n) (i : Fin 4) : z.val i ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm (scaledLatticePoint n z) i).trans (hbound _ z.property)
    change |r*(z.val i:ℝ)| ≤ B at hi
    rw [abs_mul,abs_of_pos hr] at hi
    have ha : |(z.val i:ℝ)| ≤ B/r := (le_div_iff₀ hr).mpr (by nlinarith)
    have hM : B/r ≤ (M:ℝ) := Int.le_ceil _
    have hpair := abs_le.mp (ha.trans hM)
    constructor
    · exact_mod_cast hpair.1
    · exact_mod_cast hpair.2
  let f : SourceGrid U n → (Fin 4 → Icc (-M) M) := fun z i ↦ ⟨z.val i,hcoords z i⟩
  apply Finite.of_injective f
  intro z w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalWaveSupportCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped Topology
noncomputable section

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

theorem LocalCompactWaveData.uniform_support_core (a : LocalCompactWaveData g w S D m J K k0)
    (hD : IsCompact D) {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ C : Set _root_.OAI.Yau.Jets.Coord, IsCompact C ∧ C ⊆ Ω ∧ D ⊆ interior C ∧
      ∀ᶠ n : ℕ in atTop, ∀ t : a.cover.Parameter × Fin 3,
        tsupport (a.beams.wave (n:ℝ) t) ⊆ C ∧
        ∀ x ∉ C, ∀ k : ℕ,
          iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (a.beams.wave (n:ℝ) t) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*a.beams.wave (n:ℝ) t z) x = 0 := by
  obtain ⟨C,hC,hDC,hCΩ⟩ := exists_compact_between hD hΩ hDΩ
  obtain ⟨ε,hε,hth⟩ := hD.exists_cthickening_subset_open isOpen_interior hDC
  have hsmall : ∀ᶠ n : ℕ in atTop, a.beams.R*(n:ℝ)^(-1/3:ℝ) < ε := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ a.beams.R*N^(-1/3:ℝ) < ε)
    have ht : Tendsto (fun N : ℝ ↦ a.beams.R*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul a.beams.R
    exact ht.eventually (gt_mem_nhds hε)
  refine ⟨C,hC,hCΩ,hDC,?_⟩
  filter_upwards [a.estimates,hsmall] with n hn hnε
  intro t
  have hsup : tsupport (a.beams.wave (n:ℝ) t) ⊆ C := by
    intro x hx
    have hb := (norm_le_sourceEuclideanNorm (x-coverSourceCenter a.cover t.1)).trans
      ((hn t).2.2.2.1 hx)
    have hc : coverSourceCenter a.cover t.1 ∈ D := (a.cover.center t.1).property
    apply interior_subset (hth (mem_cthickening_of_dist_le x (coverSourceCenter a.cover t.1) ε D hc ?_))
    rw [dist_eq_norm]
    exact (hb.trans_lt hnε).le
  refine ⟨hsup,?_⟩
  intro x hx k
  exact source_residual_derivative_zero g w _ _ x (fun hz ↦ hx (hsup hz)) k

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_LatticeResidualSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

theorem LocalCompactWaveData.lattice_residual_support
    (a : LocalCompactWaveData g w S D m J K k0)
    (hD : IsCompact D) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ C : Set _root_.OAI.Yau.Jets.Coord, IsCompact C ∧ C ⊆ Ω ∧ D ⊆ interior C ∧
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
        letI := hfin
        ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
          let u := gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
          tsupport u ⊆ C ∧
          tsupport (fun z ↦ sourceWeightedOperator g w (fun x ↦ (u x : ℂ)) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u z:ℂ)) ⊆ C ∧
          ∀ x ∉ C, ∀ k : ℕ,
            iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (fun x ↦ (u x:ℂ)) z +
              ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u z:ℂ)) x = 0 := by
  obtain ⟨C,hC,hCΩ,hDC,hcore⟩ := a.uniform_support_core hD hΩ hDΩ
  refine ⟨C,hC,hCΩ,hDC,?_⟩
  filter_upwards [hcore,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hVs (i : SourceGrid U n × Fin 3) : tsupport (V i) ⊆ C :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  have hu := gaussianWaveField_tsupport_subset V coeff hC.isClosed hVs
  have hc := complexified_tsupport_subset (gaussianWaveField V coeff) hC.isClosed hu
  refine ⟨hu,source_residual_tsupport_subset g w _ _ hC.isClosed hc,?_⟩
  intro x hx k
  exact source_residual_derivative_zero g w _ _ x (fun hz ↦ hx (hc hz)) k

end
end Yau.Geometry

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

local instance intrinsicCorrectedChartLocalInst1_r356339_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst2_r356339_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst3_r356339_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst4_r356339_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance intrinsicCorrectedChartLocalInst5_r356339_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance intrinsicCorrectedChartLocalInst6_r356339_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst7
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst8
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst9
local instance intrinsicCorrectedChartLocalInst10_r356339_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.intrinsicCorrectedChartLocalInst11
local instance intrinsicCorrectedChartLocalInst12_r356339_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance intrinsicCorrectedChartLocalInst13_r356339_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance intrinsicCorrectedChartLocalInst14_r356339_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance intrinsicCorrectedChartLocalInst15_r356339_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance intrinsicCorrectedChartLocalInst16_r356339_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
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

theorem round_tensor_coordinate_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (J : ℕ) :
    ∃ C > 0, ∀ (alpha : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ alpha → tsupport alpha ⊆ Q →
      ∀ (a : Base → ℝ), (∀ x, a (seedSphereFromCoord x) = alpha x) →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x i, i ≤ J → ‖iteratedFDeriv ℝ i alpha x‖ ≤ eps) →
      ∀ x i j k, i ≤ J →
        ‖iteratedFDeriv ℝ i
          (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation a) seedPoint (seedCoordEquiv y) j k) x‖ ≤
          C*eps := by
  obtain ⟨C,hC,hbound⟩ := compact_multiplier_frequency_bound roundCoordFactor roundCoordFactor_smooth hQ J
  refine ⟨C,hC,?_⟩
  intro alpha hs hsup a ha eps heps hb x i j k hi
  have hprod (x : Yau.Jets.Coord) :
      ‖iteratedFDeriv ℝ i (fun y ↦ roundCoordFactor y*alpha y) x‖ ≤ C*eps := by
    by_cases hx : x ∈ Q
    · simpa using hbound alpha hs 1 eps (by norm_num) heps 0 x hx
        (fun l hl ↦ by simpa using hb x l hl) i hi
    · have hz : alpha =ᶠ[𝓝 x] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsup h))
      have hz' : (fun y ↦ roundCoordFactor y*alpha y) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
        filter_upwards [hz] with y hy
        simp [hy]
      rw [(hz'.iteratedFDeriv ℝ i).eq_of_nhds]
      simpa using mul_nonneg hC.le heps
  simp_rw [roundTensorPerturbation_seed_entry,ha]
  by_cases hj : j=k
  · simpa [hj] using hprod x
  · simp [hj]
    positivity

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeSphereExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ}
variable {w S : Yau.Jets.Coord → ℝ} {D U : Set Yau.Jets.Coord} {m J K k0 : ℕ}
variable (b : LocalCompactWaveData g w S D m J K k0)

theorem literal_lattice_sphere_extension (hD : IsCompact D) (hUD : U ⊆ D)
    (hUb : Bornology.IsBounded U) {Ω : Set Yau.Jets.Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ Q : Set Yau.Jets.Coord, IsCompact Q ∧ Q ⊆ Ω ∧
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
        letI := hfin
        ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
          let v := gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave b.cover b.beams hUD n i.1 i.2) coeff
          ContDiff ℝ ∞ (fun x ↦ seedCoordinateField n x+v x) →
          ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧
            tsupport (u-sphericalSeed n) ⊆ seedSphereFromCoord '' Q ∧
            ∀ x, u (seedSphereFromCoord x) = seedCoordinateField n x+v x := by
  obtain ⟨Q,hQ,hQΩ,hDQ,hbound⟩ := b.lattice_residual_support hD hUD hUb hΩ hDΩ
  refine ⟨Q,hQ,hQΩ,?_⟩
  filter_upwards [hbound] with n hn
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff v hu
  have hv : ContDiff ℝ ∞ v := by
    have he : v = fun x ↦ (seedCoordinateField n x+v x)-seedCoordinateField n x := by
      funext x; ring
    rw [he]
    exact hu.sub (seedCoordinateField_smooth n)
  have hs := (hb coeff).1
  obtain ⟨u,hus,hup,hval⟩ := seed_plus_compact_sphere_field v hv
    (hQ.of_isClosed_subset isClosed_closure hs) n
  exact ⟨u,hus,hup.trans (image_mono hs),hval⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IntrinsicPackedPositiveSphereStage
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
attribute [local instance] intrinsicUniformPositiveSphereStageLocalInst1 intrinsicUniformPositiveSphereStageLocalInst2 intrinsicUniformPositiveSphereStageLocalInst3 intrinsicUniformPositiveSphereStageLocalInst4 intrinsicUniformPositiveSphereStageLocalInst5 intrinsicUniformPositiveSphereStageLocalInst6 intrinsicUniformPositiveSphereStageLocalInst7 intrinsicUniformPositiveSphereStageLocalInst8 intrinsicUniformPositiveSphereStageLocalInst9 intrinsicUniformPositiveSphereStageLocalInst10 intrinsicUniformPositiveSphereStageLocalInst11 intrinsicUniformPositiveSphereStageLocalInst12 intrinsicUniformPositiveSphereStageLocalInst13 intrinsicUniformPositiveSphereStageLocalInst14 intrinsicUniformPositiveSphereStageLocalInst15 intrinsicUniformPositiveSphereStageLocalInst16

theorem intrinsic_packed_positive_sphere_stage_oai :
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
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (J0 : ℕ),
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
              IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation ag x) ∧
              (∀ x v w, (A x+roundTensorPerturbation ag x) v w =
                (A x+roundTensorPerturbation ag x) w v) ∧
              (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation ag x) v v) ∧
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+bg x) ∧
              (∀ x, 0 < rho x+bg x) ∧ ug ≠ 0 ∧
              (∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
                (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x)) ∧
              (∀ x i j k, i ≤ J0 →
                ‖iteratedFDeriv ℝ i (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation ag)
                  seedPoint (seedCoordEquiv y) j k) x‖ ≤ C*((n:ℝ)^2)⁻¹) ∧
              ∀ p z, (extChartAt (𝓡 4) p).symm z ∉ K ∪ seedSphereFromCoord '' (Q ∪ Qw) →
                -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation ag x)
                  (fun x ↦ rho x+bg x) ug p z = seedEigenvalue n*ug ((extChartAt (𝓡 4) p).symm z) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_small_corrected_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨c,hc,hstage⟩ := hstage A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  refine ⟨c,hc,?_⟩
  intro T J0 k0 K'
  obtain ⟨d,b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hselect⟩ :=
    hstage T J0
  obtain ⟨Qw,hQw,hQwΩ,hext⟩ := literal_lattice_sphere_extension b d.compact_closure_U
    subset_closure (d.compact_closure_U.isBounded.subset subset_closure) d.open_Ω d.closure_U_Ω
  obtain ⟨B,hB,htensor⟩ := round_tensor_coordinate_bound hQ J0
  let D := (1+B)*C
  have hCD : C ≤ D := by dsimp [D] <;> nlinarith
  obtain ⟨eta,heta,hcorr⟩ := positive_sphere_scalar_correction A hAs hs hp rho hrs hrp
  refine ⟨d,b,hb,D,by dsimp [D] <;> positivity,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hselect,hext,eventually_inverse_square_small C eta heta,eventually_gt_atTop (0:ℕ)] with n hn hnExt hnSmall hn0
  obtain ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,hsize,heq⟩ := hn
  obtain ⟨hfin',hExt⟩ := hnExt
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  obtain ⟨ug,hug,hugs,hugval⟩ := hExt coeff hu
  have heps : 0 ≤ C*((n:ℝ)^2)⁻¹ := by positivity
  have hab (x : Yau.Jets.Coord) := hsize x 0 (Nat.zero_le J0)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hab
  obtain ⟨ag,bg,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,hnew,hnewSym,hnewPos,hrnew,hrnewPos⟩ :=
    hcorr _ _ Q hQ halpha hbeta has hbs _ heps hnSmall
      (fun x ↦ (le_add_of_nonneg_right (abs_nonneg _)).trans (hab x))
      (fun x ↦ (le_add_of_nonneg_left (abs_nonneg _)).trans (hab x))
  have hbound : C*((n:ℝ)^2)⁻¹ ≤ D*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_right hCD (by positivity)
  have hten := htensor _ halpha has ag hagval _ heps
    (fun x i hi ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans (hsize x i hi))
  have hfixed := corrected_seed_chart_equation A hAs hs hp rho hrp ug hug (seedEigenvalue n)
    ag bg hnew hnewSym hnewPos hrnewPos
  have hfixed' : ∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
      (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x) := by
    apply hfixed
    intro x
    simp_rw [hagval,hbgval,hugval]
    exact heq x
  have hugne : ug ≠ 0 := by
    intro hz
    have h0 : (0 : Yau.Jets.Coord) ∈ seedCoordCube a := by
      constructor <;> intro i <;> simp <;> linarith
    have h0Ω := subset_closure (d.closure_U_Ω (subset_closure (d.C_U (d.inner_C (Or.inl h0)))))
    have hj := hjet 0 h0Ω
    have hzero : (fun x ↦ seedCoordinateField n x + gaussianWaveField
        (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x) =
        (fun _ ↦ (0:ℝ)) := by
      funext x
      rw [← hugval x,hz]
      rfl
    rw [hzero] at hj
    simp [sourceFirstJetSize,sourceEuclideanNorm] at hj
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    have hh : 0 < ((n:ℝ)^65)⁻¹ * max (Real.exp ((n:ℝ)*d.S 0))
        (Real.exp ((n:ℝ)*seedCoordReal 0)) :=
      mul_pos (by positivity) ((Real.exp_pos _).trans_le (le_max_left _ _))
    linarith
  refine ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,
    (fun x i hi ↦ (hsize x i hi).trans hbound),heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,
    (fun x ↦ (hagB x).trans hbound),(fun x ↦ (hbgB x).trans hbound),
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed',?_,?_⟩
  · intro x i j k hi
    refine (hten x i j k hi).trans ?_
    have hBD : B*C ≤ D := by dsimp [D] <;> nlinarith
    calc
      B*(C*((n:ℝ)^2)⁻¹) = (B*C)*((n:ℝ)^2)⁻¹ := by ring
      _ ≤ D*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_right hBD (by positivity)
  · exact corrected_exterior_equation A rho hK.isClosed
      ((hQ.union hQw).image seedSphereFromCoord_continuous).isClosed hA hrho ag bg ug n
      (hags.trans (image_mono subset_union_left)) (hbgs.trans (image_mono subset_union_left))
      (hugs.trans (image_mono subset_union_right))

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_packed_positive_sphere_stage_oai := @OAI.Yau.Target.intrinsic_packed_positive_sphere_stage_oai
