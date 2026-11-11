-- Prove2me | solution 1 for OAI.Yau.Target.sphere_reference_literal_nodal_persistence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:36:04.913201+00:00
-- url     : https://prove2.me/submissions/059b4241-eed2-4244-b5fa-e2b58d9e1c92

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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_sphere_finite_norm_simple_oriented_persistence
import Theorems.Thm_OAI_Yau_Target_uniform_intrinsic_coefficient_nodal_transfer

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IndependentWeightedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma weightedBaseMatrix_inverse {A : Matrix n n ℝ} (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : (weightedBaseMatrix A rho)⁻¹ = rho⁻¹ • A := by
  let : Invertible rho := invertibleOfNonzero hr.ne'
  rw [weightedBaseMatrix,Matrix.inv_smul A⁻¹ rho (isUnit_iff_ne_zero.mpr hA.inv.det_pos.ne'),
    invOf_eq_inv,Matrix.nonsing_inv_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TangentialMatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma radial_fixed_inverse (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : n → ℝ) (hx : A *ᵥ x = x) : A⁻¹ *ᵥ x = x := by
  calc
    A⁻¹ *ᵥ x = A⁻¹ *ᵥ (A *ᵥ x) := congrArg (fun v ↦ A⁻¹ *ᵥ v) hx.symm
    _ = x := by
      rw [mulVec_mulVec,A.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RadialVolumeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

local instance instDecidableEqFinOfNatNat_solutions_ref6fe8_1 : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
attribute [local instance] OAI.Yau.Geometry.instFintypeFinOfNatNat_solutions
lemma radialVolumeMatrix_tangent (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (x v : Fin 5 → ℝ) (hv : x ⬝ᵥ v = 0) :
    radialVolumeMatrix A rho x *ᵥ v = weightedBaseMatrix A rho *ᵥ v := by
  rw [radialVolumeMatrix,add_mulVec,← mulVec_mulVec,replicateRow_mulVec_eq_const,hv]
  simp

lemma radialVolumeMatrix_radial (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (rho : ℝ) (x : Fin 5 → ℝ) (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    radialVolumeMatrix A rho x *ᵥ x = x := by
  simp only [radialVolumeMatrix,add_mulVec,weightedBaseMatrix,smul_mulVec,
    radial_fixed_inverse A hA x hx,← mulVec_mulVec,replicateRow_mulVec_eq_const,hn]
  ext i
  simp [mulVec,dotProduct]
  ring

lemma radialVolumeMatrix_det (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) :
    (radialVolumeMatrix A rho x).det = rho^4 / A.det := by
  have hh := weightedBaseMatrix_posDef hA hr
  rw [radialVolumeMatrix,det_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),weightedBaseMatrix_inverse hA hr]
  rw [Matrix.mul_assoc,← replicateCol_mulVec,smul_mulVec,mulVec_smul,hx,
    replicateRow_mul_replicateCol]
  conv_lhs => arg 2; rw [det_unique]

  simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.of_apply,
    dotProduct_smul,hn,smul_eq_mul,mul_one]
  rw [weightedBaseMatrix,Matrix.det_smul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  simp only [Fintype.card_fin]
  field_simp
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TangentGramDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

lemma rectangular_congruence_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : n ≃ m)
    (R : Matrix m m ℝ) (F : Matrix m n ℝ) :
    (F.transpose * R * F).det = R.det * (F.transpose * F).det := by
  let G := F.submatrix e id
  have h : G.transpose * R.submatrix e e * G = F.transpose * R * F := by
    simp only [G,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id]
  have h0 : G.transpose * G = F.transpose * F := by
    simp only [G,transpose_submatrix,submatrix_mul_equiv,submatrix_id_id]
  rw [← h,← h0]
  simp only [det_mul,det_transpose,det_submatrix_equiv_self]
  ring

lemma augmented_gram_det {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] [Unique k]
    (R : Matrix m m ℝ) (J : Matrix m n ℝ) (x : m → ℝ)
    (hx : R *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    ((fromCols J (replicateCol k x)).transpose * R *
      fromCols J (replicateCol k x)).det = (J.transpose * R * J).det := by
  rw [transpose_fromCols,fromRows_mul,fromRows_mul_fromCols]
  have ht : J.transpose * R * replicateCol k x = 0 := by
    rw [Matrix.mul_assoc,← replicateCol_mulVec,hx,← replicateCol_mulVec,hJ]
    rfl
  have hb : (replicateCol k x).transpose * R * replicateCol k x = 1 := by
    rw [Matrix.mul_assoc,← replicateCol_mulVec,hx]
    ext i j
    simpa [mul_apply,replicateCol,dotProduct,Matrix.one_apply,Subsingleton.elim i j] using hn
  rw [ht,hb,det_fromBlocks_zero₁₂,det_one,mul_one]

lemma tangent_gram_det {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k] [Unique k]
    (e : (n ⊕ k) ≃ m) (R : Matrix m m ℝ) (J : Matrix m n ℝ) (x : m → ℝ)
    (hx : R *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    (J.transpose * R * J).det = R.det * (J.transpose * J).det := by
  have h := rectangular_congruence_det e R (fromCols J (replicateCol k x))
  rw [augmented_gram_det R J x hx hn hJ] at h
  have h0 := augmented_gram_det (k := k) (1 : Matrix m m ℝ) J x
    (one_mulVec x) hn hJ
  simp only [Matrix.mul_one] at h0
  rwa [h0] at h

attribute [local instance] OAI.Yau.Geometry.instDecidableEqFinOfNatNat_solutions_1
attribute [local instance] OAI.Yau.Geometry.instFintypeFinOfNatNat_solutions_1
lemma radial_tangent_gram_det (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (x : Fin 5 → ℝ) (J : Matrix (Fin 5) (Fin 4) ℝ)
    (hx : A *ᵥ x = x) (hn : x ⬝ᵥ x = 1) (hJ : J.transpose *ᵥ x = 0) :
    (J.transpose * weightedBaseMatrix A rho * J).det =
      (rho^4 / A.det) * (J.transpose * J).det := by
  have hcol (j : Fin 4) : x ⬝ᵥ (fun i ↦ J i j) = 0 := by
    have h := congrFun hJ j
    simpa only [mulVec,transpose_apply,Pi.zero_apply,dotProduct_comm] using h
  have he : radialVolumeMatrix A rho x * J = weightedBaseMatrix A rho * J := by
    ext i j
    exact congrFun (radialVolumeMatrix_tangent A rho x (fun i ↦ J i j) (hcol j)) i
  have h := tangent_gram_det (finSumFinEquiv : (Fin 4 ⊕ Fin 1) ≃ Fin 5)
    (radialVolumeMatrix A rho x) J x (radialVolumeMatrix_radial A hA rho x hx hn) hn hJ
  rw [radialVolumeMatrix_det A hA hr x hx hn,Matrix.mul_assoc,he,← Matrix.mul_assoc] at h
  exact h

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

attribute [local instance] OAI.Yau.Target.instFactEqNatFinrankRealAmbientBaseHAddOfNat_2
lemma sphere_radial_dot (x : Base) :
    (fun i ↦ (x : AmbientBase) i) ⬝ᵥ (fun i ↦ (x : AmbientBase) i) = 1 := by
  have hn := mem_sphere_zero_iff_norm.mp x.property
  have h := real_inner_self_eq_norm_sq (x : AmbientBase)
  rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hn,one_pow] at h
  exact h

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleChartFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
noncomputable section
attribute [local instance] finrank_real_complex_fact'

lemma circleChartDerivative_injective (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    Function.Injective (circleChartDerivative p y) := by
  apply (injective_mvfderiv_subtypeVal_sphere (n := 1) ((extChartAt (𝓡 1) p).symm y)).comp
  have h := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 1) hy).injective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

lemma circleChartFactor_pos (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) : 0 < circleChartFactor p y := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  have he := circleChartDerivative_injective p hy (h.trans (map_zero _).symm)
  exact (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.ne_zero 0 he

lemma circleChartDerivative_inner_basis (p : Circle) (y : CircleModel) (i j : Fin 1) :
    @inner ℝ ℂ _ (circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ i))
      (circleChartDerivative p y (EuclideanSpace.basisFun (Fin 1) ℝ j)) =
      circleChartFactor p y := by
  rw [Subsingleton.elim i 0,Subsingleton.elim j 0,real_inner_self_eq_norm_sq]
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartFrameSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
attribute [local instance] finrank_real_complex_fact'

attribute [local instance] OAI.Yau.Target.instFactEqNatFinrankRealAmbientBaseHAddOfNat_3
lemma circleChartDerivative_eq_fderiv (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    circleChartDerivative p y =
      fderiv ℝ ((fun z : Circle ↦ (z : ℂ)) ∘ (extChartAt (𝓡 1) p).symm) y := by
  exact (inverse_chart_comp_derivative _ (contMDiff_coe_sphere (E := ℂ) (n := 1)) p hy).symm

lemma circleChartDerivative_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (circleChartDerivative p) y := by
  apply (smooth_inverse_chart_derivative _ (contMDiff_coe_sphere (E := ℂ) (n := 1)) p hy).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with z hz
  exact circleChartDerivative_eq_fderiv p hz

lemma circleChartFactor_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (circleChartFactor p) y := by
  have h := (circleChartDerivative_smooth_at p hy).clm_apply
    (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 1) ℝ 0))
  convert! h.inner ℝ h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [real_inner_self_eq_norm_sq]
  rfl

lemma circleChartDensity_smooth_at (p : Circle) {y : CircleModel}
    (hy : y ∈ (extChartAt (𝓡 1) p).target) :
    ContDiffAt ℝ ∞ (fun z ↦ Real.sqrt (circleChartFactor p z)) y :=
  (circleChartFactor_smooth_at p hy).sqrt (circleChartFactor_pos p hy).ne'

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

lemma product_chart_inverse_derivative (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y =
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p.1).symm y.1).prodMap
      (mfderiv 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p.2).symm y.2) := by
  have hb : MDifferentiableAt 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p.1).symm y.1 := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 4) (product_chart_target p hy).1
    rw [ModelWithCorners.range_eq_univ,mdifferentiableWithinAt_univ] at h
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
  have hc : MDifferentiableAt 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p.2).symm y.2 := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 1) (product_chart_target p hy).2
    rw [ModelWithCorners.range_eq_univ,mdifferentiableWithinAt_univ] at h
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
  rw [show 𝓘(ℝ,Model) = 𝓘(ℝ,BaseModel).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod]
  convert! mfderiv_prodMap hb hc using 1
  all_goals try with_reducible_and_instances rfl

lemma product_chart_embedding_derivative (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (v : Model) :
    mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding ((extChartAt modelWithCorners p).symm y)
      (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y v) =
      (sphereChartDerivative p.1 y.1 v.1,circleChartDerivative p.2 y.2 v.2) := by
  rw [targetEmbedding_derivative,product_chart_inverse_derivative p hy]
  rfl

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

lemma independentAmbientMetric_productMatrix
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y =
      fromBlocks (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
        (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1) 0 0
        (Matrix.of fun _ _ : Fin 1 ↦
          (ambientCircleWeight (A ((extChartAt (𝓡 4) p.1).symm y.1))
            (rho ((extChartAt (𝓡 4) p.1).symm y.1)))^2 * circleChartFactor p.2 y.2) := by
  ext i j
  change warpedAmbientForm _ _
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding _
      (mfderiv 𝓘(ℝ,Model) modelWithCorners _ y (productFrame i)))
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding _
      (mfderiv 𝓘(ℝ,Model) modelWithCorners _ y (productFrame j))) = _
  rw [product_chart_embedding_derivative p hy,product_chart_embedding_derivative p hy,
    warpedAmbientForm_apply]
  have hpnt : ((extChartAt modelWithCorners p).symm y).1 =
      (extChartAt (𝓡 4) p.1).symm y.1 := by
    rw [extChartAt_prod]
    rfl
  rw [hpnt]
  cases i <;> cases j <;>
    simp only [productFrame,Module.Basis.prod_apply_inl_fst,Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_fst,Module.Basis.prod_apply_inr_snd,
      OrthonormalBasis.coe_toBasis,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.of_apply,
      map_zero,inner_zero_left,inner_zero_right,mul_zero,zero_add,add_zero,
      sphereWeightedChartMatrix_apply,circleChartDerivative_inner_basis]
  all_goals simp

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

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

include hr in
lemma baseChartDensity_smooth_at (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (baseChartDensity rho p) z :=
  (smooth_inverse_chart_comp rho hr p hz).mul (roundChartDensity_smooth_at p hz)

include hA hp hr hrp in
lemma baseChartFlux_smooth_at (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) (i : Fin 4) :
    ContDiffAt ℝ ∞ (baseChartFlux A rho f p i) z := by
  apply (baseChartDensity_smooth_at rho hr p hz).mul
  apply ContDiffAt.sum
  intro j _
  exact (baseChartMetric_inverse_smooth_at A rho hA hp hr hrp p hz i j).mul
    ((smooth_inverse_chart_derivative f hf p hz).clm_apply contDiffAt_const)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleInvariantDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma circleLift_chart (f : Base → ℝ) (p : Manifold5) :
    circleLift f ∘ (extChartAt modelWithCorners p).symm =
      (f ∘ (extChartAt (𝓡 4) p.1).symm) ∘ Prod.fst := by
  rw [extChartAt_prod]
  rfl

lemma circleLift_chart_derivative (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    fderiv ℝ (circleLift f ∘ (extChartAt modelWithCorners p).symm) y =
      (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p.1).symm) y.1).comp
        (ContinuousLinearMap.fst ℝ BaseModel CircleModel) := by
  rw [circleLift_chart,fderiv_comp y
    ((smooth_inverse_chart_comp f hf p.1 (product_chart_target p hy).1).differentiableAt (by simp))
    differentiableAt_fst,fderiv_fst]

lemma circleLift_product_covector (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    fderiv ℝ (circleLift f ∘ (extChartAt modelWithCorners p).symm) y (productFrame i) =
      Sum.elim (fun j ↦ fderiv ℝ (f ∘ (extChartAt (𝓡 4) p.1).symm) y.1
        (EuclideanSpace.basisFun (Fin 4) ℝ j)) (fun _ ↦ 0) i := by
  rw [circleLift_chart_derivative f hf p hy]
  cases i <;> simp [productFrame]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma constant_matrix_flux_derivative (D : Matrix n n ℝ) (F : n → E → ℝ)
    {x : E} (hF : ∀ a, DifferentiableAt ℝ (F a) x) (i : n) (v : E) :
    fderiv ℝ (fun y ↦ ∑ a, D i a * F a y) x v =
      ∑ a, D i a * fderiv ℝ (F a) x v := by
  rw [show (fun y ↦ ∑ a, D i a * F a y) =
    ∑ a, (fun y ↦ D i a * F a y) by ext y; simp]
  rw [fderiv_sum (fun a _ ↦ (hF a).const_mul (D i a))]
  simp only [_root_.sum_apply,fderiv_const_mul (hF _) _,
    _root_.smul_apply,smul_eq_mul]

omit [DecidableEq n] in
lemma basis_divergence_change (b c : Module.Basis n ℝ E) (F : n → E → ℝ)
    {x : E} (hF : ∀ a, DifferentiableAt ℝ (F a) x) :
    ∑ i, fderiv ℝ (fun y ↦ ∑ a, c.toMatrix b i a * F a y) x (c i) =
      ∑ a, fderiv ℝ (F a) x (b a) := by
  simp_rw [constant_matrix_flux_derivative _ F hF]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [← c.sum_toMatrix_smul_self b a]
  simp only [map_sum,map_smul,smul_eq_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeparatedCircleDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m : Type*} [Fintype n] [Fintype m]

lemma separated_factor_horizontal_derivative (a : E → ℝ) (k : F → ℝ)
    {x : E} {t : F} (ha : DifferentiableAt ℝ a x) (hk : DifferentiableAt ℝ k t) (v : E) :
    fderiv ℝ (fun y : E × F ↦ k y.2 * a y.1) (x,t) (v,0) =
      k t * fderiv ℝ a x v := by
  have ha' : DifferentiableAt ℝ (fun y : E × F ↦ a y.1) (x,t) :=
    ha.comp (x,t) differentiableAt_fst
  have hk' : DifferentiableAt ℝ (fun y : E × F ↦ k y.2) (x,t) :=
    hk.comp (x,t) differentiableAt_snd
  rw [show (fun y : E × F ↦ k y.2 * a y.1) =
    (fun y : E × F ↦ k y.2) * (fun y : E × F ↦ a y.1) by rfl, fderiv_mul hk' ha']
  have hd1 : fderiv ℝ (fun y : E × F ↦ a y.1) (x,t) =
      (fderiv ℝ a x).comp (ContinuousLinearMap.fst ℝ E F) := by
    rw [show (fun y : E × F ↦ a y.1) = a ∘ Prod.fst from rfl]
    convert! fderiv_comp (𝕜 := ℝ) (f := Prod.fst) (g := a) (x,t) ha differentiableAt_fst using 1
    all_goals try with_reducible_and_instances rfl
    simp only [fderiv_fst]
  have hd2 : fderiv ℝ (fun y : E × F ↦ k y.2) (x,t) =
      (fderiv ℝ k t).comp (ContinuousLinearMap.snd ℝ E F) := by
    rw [show (fun y : E × F ↦ k y.2) = k ∘ Prod.snd from rfl]
    convert! fderiv_comp (𝕜 := ℝ) (f := Prod.snd) (g := k) (x,t) hk differentiableAt_snd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [fderiv_snd]
  rw [hd1,hd2]
  simp

lemma separated_factor_divergence (b : Module.Basis n ℝ E) (c : Module.Basis m ℝ F)
    (a : n → E → ℝ) (k : F → ℝ) {x : E} {t : F}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hk : DifferentiableAt ℝ k t) :
    ∑ i : n ⊕ m, fderiv ℝ
      (fun y : E × F ↦ Sum.elim (fun j ↦ k y.2 * a j y.1) (fun _ ↦ 0) i)
      (x,t) ((b.prod c) i) = k t * ∑ i, fderiv ℝ (a i) x (b i) := by
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  have hb (i : n) : (b.prod c) (Sum.inl i) = (b i,0) := by
    ext <;> simp
  simp_rw [hb]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,Finset.sum_const_zero,add_zero]
  simp_rw [separated_factor_horizontal_derivative _ k (ha _) hk]
  rw [Finset.mul_sum]

lemma separated_density_cancellation (b : Module.Basis n ℝ E) (c : Module.Basis m ℝ F)
    (a : n → E → ℝ) (k : F → ℝ) (d : ℝ) {x : E} {t : F}
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hk : DifferentiableAt ℝ k t) (hkp : k t ≠ 0) :
    (d*k t)⁻¹ * ∑ i : n ⊕ m, fderiv ℝ
      (fun y : E × F ↦ Sum.elim (fun j ↦ k y.2 * a j y.1) (fun _ ↦ 0) i)
      (x,t) ((b.prod c) i) = d⁻¹ * ∑ i, fderiv ℝ (a i) x (b i) := by
  rw [separated_factor_divergence b c a k ha hk,_root_.mul_inv_rev]
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))

include hrad

lemma independentAmbientMetric_product_det (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det =
      (rho ((extChartAt (𝓡 4) p.1).symm y.1))^2 *
        (sphereRoundChartMatrix p.1 y.1).det * circleChartFactor p.2 y.2 := by
  rw [independentAmbientMetric_productMatrix A rho hA hp hr hrp p hy,
    det_fromBlocks_zero₂₁,det_fin_one]
  dsimp only [Matrix.of_apply]
  have he := radial_tangent_gram_det _ (hp _) (hrp ((extChartAt (𝓡 4) p.1).symm y.1)) _ (sphereChartFrame p.1 y.1)
    (hrad _) (sphere_radial_dot _) (sphereChartFrame_orthogonal p.1 y.1)
  change (sphereWeightedChartMatrix _ _ _ _).det = _ at he
  rw [he,ambientCircleWeight,div_pow,Real.sq_sqrt (hp _).det_pos.le]
  have halg (r d H k : ℝ) (hr0 : r ≠ 0) (hd0 : d ≠ 0) :
      (r^4/d)*H*(d/r^2*k) = r^2*H*k := by
    field_simp
  convert! halg _ _ _ _ (hrp ((extChartAt (𝓡 4) p.1).symm y.1)).ne'
    (hp ((extChartAt (𝓡 4) p.1).symm y.1)).det_pos.ne' using 1
  all_goals try with_reducible_and_instances rfl

lemma independentAmbientMetric_product_volume (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    Real.sqrt (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det =
      rho ((extChartAt (𝓡 4) p.1).symm y.1) *
        Real.sqrt (sphereRoundChartMatrix p.1 y.1).det * Real.sqrt (circleChartFactor p.2 y.2) := by
  rw [independentAmbientMetric_product_det A rho hA hp hr hrp hrad p hy,
    Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sphereRoundChartMatrix_posDef p.1 (product_chart_target p hy).1).det_pos.le),
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (hrp _).le]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ProductChartFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma positive_circle_block_inverse {H : Matrix (Fin 4) (Fin 4) ℝ} (hH : H.PosDef)
    {d : ℝ} (hd : 0 < d) :
    (fromBlocks H 0 0 (Matrix.of (fun _ _ : Fin 1 ↦ d)))⁻¹ =
      fromBlocks H⁻¹ 0 0 (Matrix.of (fun _ _ : Fin 1 ↦ d))⁻¹ := by
  have hD : IsUnit (Matrix.of (fun _ _ : Fin 1 ↦ d)) := by
    rw [Matrix.isUnit_iff_isUnit_det,det_fin_one]
    exact isUnit_iff_ne_zero.mpr hd.ne'
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff H 0 _ (iff_of_true hH.isUnit hD)]
  simp

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

lemma independentAmbientMetric_product_inverse (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y)⁻¹ =
      fromBlocks (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
        (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1)⁻¹ 0 0
        (Matrix.of fun _ _ : Fin 1 ↦
          (ambientCircleWeight (A ((extChartAt (𝓡 4) p.1).symm y.1))
            (rho ((extChartAt (𝓡 4) p.1).symm y.1)))^2 * circleChartFactor p.2 y.2)⁻¹ := by
  rw [independentAmbientMetric_productMatrix A rho hA hp hr hrp p hy]
  apply positive_circle_block_inverse
    (sphereWeightedChartMatrix_posDef _ (hp _) (hrp _) p.1 (product_chart_target p hy).1)
  exact mul_pos (sq_pos_of_pos (ambientCircleWeight_pos _ (hp _) (hrp _)))
    (circleChartFactor_pos p.2 (product_chart_target p hy).2)

lemma independentAmbientMetric_product_flux
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (p : Manifold5) {y : Model} (hy : y ∈ (extChartAt modelWithCorners p).target)
    (v : Fin 4 → ℝ) (i : Fin 4 ⊕ Fin 1) :
    Real.sqrt (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det *
      ∑ j, (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y)⁻¹ i j *
        Sum.elim v (fun _ ↦ 0) j =
    Sum.elim (fun a ↦ Real.sqrt (circleChartFactor p.2 y.2) *
      (rho ((extChartAt (𝓡 4) p.1).symm y.1) * Real.sqrt (sphereRoundChartMatrix p.1 y.1).det *
        ∑ b, (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
          (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1)⁻¹ a b * v b)) (fun _ ↦ 0) i := by
  rw [independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy,
    independentAmbientMetric_product_inverse A rho hA hp hr hrp p hy]
  cases i with
  | inl a =>
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,fromBlocks_apply₁₁,
      fromBlocks_apply₁₂,mul_zero,Finset.sum_const_zero,add_zero]
    ring
  | inr a => simp [Fintype.sum_sum_type,Matrix.fromBlocks]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

lemma basis_change_det_ne_zero (b c : Module.Basis n ℝ E) : (b.toMatrix c).det ≠ 0 := by
  have h := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip c)
  rw [det_mul,det_one] at h
  exact (mul_ne_zero_iff.mp (h ▸ one_ne_zero)).1

lemma basis_change_inverse (b c : Module.Basis n ℝ E) : (b.toMatrix c)⁻¹ = c.toMatrix b :=
  inv_eq_left_inv (c.toMatrix_mul_toMatrix_flip b)

lemma basisMetricMatrix_change (b c : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) :
    basisMetricMatrix c B = (b.toMatrix c).transpose * basisMetricMatrix b B * b.toMatrix c :=
  (LinearMap.toMatrix₂_mul_basis_toMatrix b b c c B).symm

lemma basisMetricMatrix_volume_change (b c : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) :
    Real.sqrt (basisMetricMatrix c B).det =
      |(b.toMatrix c).det| * Real.sqrt (basisMetricMatrix b B).det := by
  rw [basisMetricMatrix_change,det_mul,det_mul,det_transpose]
  rw [show (b.toMatrix c).det * (basisMetricMatrix b B).det * (b.toMatrix c).det =
    (b.toMatrix c).det^2 * (basisMetricMatrix b B).det by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

omit [DecidableEq n] in
lemma basis_derivative_vector (b c : Module.Basis n ℝ E) (f : E → ℝ) (y : E) :
    (fun j ↦ fderiv ℝ f y (c j)) = (b.toMatrix c).transpose *ᵥ (fun a ↦ fderiv ℝ f y (b a)) := by
  ext j
  conv_lhs => rw [← b.sum_toMatrix_smul_self c j]
  simp only [map_sum,map_smul,smul_eq_mul,mulVec,dotProduct,transpose_apply]

lemma basis_inverse_derivative_vector (b c : Module.Basis n ℝ E)
    (B : LinearMap.BilinForm ℝ E) (f : E → ℝ) (y : E) :
    (basisMetricMatrix c B)⁻¹ *ᵥ (fun j ↦ fderiv ℝ f y (c j)) =
      c.toMatrix b *ᵥ ((basisMetricMatrix b B)⁻¹ *ᵥ (fun a ↦ fderiv ℝ f y (b a))) := by
  rw [basis_derivative_vector b c f y,mulVec_mulVec,basisMetricMatrix_change b c,
    Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  have hc : IsUnit ((b.toMatrix c).transpose.det) := by
    rw [det_transpose]
    exact isUnit_iff_ne_zero.mpr (basis_change_det_ne_zero b c)
  rw [Matrix.mul_assoc,Matrix.mul_assoc,nonsing_inv_mul _ hc,Matrix.mul_one,
    basis_change_inverse, ← mulVec_mulVec]

lemma basisMetricFlux_change (b c : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (i : n) (y : E) :
    basisMetricFlux c B f i y = |(b.toMatrix c).det| *
      ∑ a, c.toMatrix b i a * basisMetricFlux b B f a y := by
  have h := congrFun (basis_inverse_derivative_vector b c (B y) f y) i
  change (∑ j, _ * _) = _ at h
  rw [basisMetricFlux,basisMetricMatrix_volume_change b c,h]
  simp only [mulVec,dotProduct,basisMetricFlux,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma basisMetricLaplacian_change (b c : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) {y : E} (hF : ∀ i, DifferentiableAt ℝ (basisMetricFlux b B f i) y) :
    basisMetricLaplacian c B f y = basisMetricLaplacian b B f y := by
  have hfun (i : n) : basisMetricFlux c B f i = fun z ↦ |(b.toMatrix c).det| *
      ∑ a, c.toMatrix b i a * basisMetricFlux b B f a z := by
    funext z; exact basisMetricFlux_change b c B f i z
  unfold basisMetricLaplacian
  simp_rw [hfun]
  have hd (i : n) : DifferentiableAt ℝ
      (fun z ↦ ∑ a, c.toMatrix b i a * basisMetricFlux b B f a z) y :=
    by
      convert! (DifferentiableAt.sum (u := Finset.univ)
        (fun a _ ↦ (hF a).const_mul (c.toMatrix b i a))) using 1
      all_goals try with_reducible_and_instances rfl
      ext z; simp
  simp_rw [fderiv_const_mul (hd _) _,_root_.smul_apply,smul_eq_mul]
  rw [← Finset.mul_sum,basis_divergence_change b c _ hF,basisMetricMatrix_volume_change b c]
  have hn := (abs_pos.mpr (basis_change_det_ne_zero b c)).ne'
  rw [_root_.mul_inv_rev]
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisLaplacianReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma basisMetricMatrix_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : LinearMap.BilinForm ℝ E) :
    basisMetricMatrix (b.reindex e) B = (basisMetricMatrix b B).submatrix e.symm e.symm := by
  ext i j
  simp [basisMetricMatrix,LinearMap.toMatrix₂_apply]

lemma basisMetricFlux_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : E → LinearMap.BilinForm ℝ E) (f : E → ℝ) (i : m) (y : E) :
    basisMetricFlux (b.reindex e) B f i y = basisMetricFlux b B f (e.symm i) y := by
  simp only [basisMetricFlux,basisMetricMatrix_reindex,det_submatrix_equiv_self,
    inv_submatrix_equiv,submatrix_apply,Module.Basis.reindex_apply]
  congr 1
  exact e.symm.sum_comp (fun j : n ↦ (basisMetricMatrix b (B y))⁻¹ (e.symm i) j *
    fderiv ℝ f y (b j))

lemma basisMetricLaplacian_reindex (b : Module.Basis n ℝ E) (e : n ≃ m)
    (B : E → LinearMap.BilinForm ℝ E) (f : E → ℝ) (y : E) :
    basisMetricLaplacian (b.reindex e) B f y = basisMetricLaplacian b B f y := by
  have hf (i : m) : basisMetricFlux (b.reindex e) B f i = basisMetricFlux b B f (e.symm i) := by
    funext z; exact basisMetricFlux_reindex b e B f i z
  simp only [basisMetricLaplacian,basisMetricMatrix_reindex,det_submatrix_equiv_self,hf,
    Module.Basis.reindex_apply]
  congr 1
  exact e.symm.sum_comp (fun j : n ↦ fderiv ℝ (basisMetricFlux b B f j) y (b j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TargetLaplacianBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma basisMetricMatrix_target (g : SmoothMetric) (c : PartialEquiv Manifold5 Model) (y : Model) :
    basisMetricMatrix frame (chartBilinearForm g c y) = metricMatrix g c y := by
  ext i j
  simp only [basisMetricMatrix,LinearMap.toMatrix₂_apply,chartBilinearForm,metricMatrix]
  rfl

lemma basisMetricMatrix_product (g : SmoothMetric) (p : Manifold5) (y : Model) :
    basisMetricMatrix productFrame (chartBilinearForm g (extChartAt modelWithCorners p) y) =
      productMetricMatrix g p y := by
  ext i j
  simp only [basisMetricMatrix,LinearMap.toMatrix₂_apply,chartBilinearForm,productMetricMatrix]
  rfl

lemma chartLaplacian_basisMetricLaplacian (g : SmoothMetric)
    (c : PartialEquiv Manifold5 Model) (u : Manifold5 → ℝ) (y : Model) :
    chartLaplacian g c u y = basisMetricLaplacian frame (chartBilinearForm g c) (u ∘ c.symm) y := by
  simp only [basisMetricLaplacian,basisMetricMatrix_target,
    chartLaplacian,volumeFactor]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext z
  simp only [basisMetricFlux,basisMetricMatrix_target]

lemma chartLaplacian_product_basis (g : SmoothMetric) (p : Manifold5)
    (u : Manifold5 → ℝ) {y : Model}
    (hF : ∀ i, DifferentiableAt ℝ
      (basisMetricFlux productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
        (u ∘ (extChartAt modelWithCorners p).symm) i) y) :
    chartLaplacian g (extChartAt modelWithCorners p) u y =
      basisMetricLaplacian productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
        (u ∘ (extChartAt modelWithCorners p).symm) y := by
  rw [chartLaplacian_basisMetricLaplacian]
  have hr (i : Index) :
      basisMetricFlux indexedProductFrame (chartBilinearForm g (extChartAt modelWithCorners p))
          (u ∘ (extChartAt modelWithCorners p).symm) i =
      basisMetricFlux productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
          (u ∘ (extChartAt modelWithCorners p).symm) (productIndexEquiv.symm i) := by
    funext z
    exact basisMetricFlux_reindex productFrame productIndexEquiv _ _ i z
  rw [basisMetricLaplacian_change indexedProductFrame frame _ _ (fun i ↦ by rw [hr]; exact hF _)]
  exact basisMetricLaplacian_reindex productFrame productIndexEquiv _ _ y

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ProductFlux
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
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)

include hrad hf

lemma circleLift_actual_product_flux (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i y =
    Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 y.2) * baseChartFlux A rho f p.1 j y.1)
      (fun _ ↦ 0) i := by
  unfold basisMetricFlux
  simp only [basisMetricMatrix_product,circleLift_product_covector f hf p hy]
  exact independentAmbientMetric_product_flux A rho hA hp hr hrp hrad p hy _ i

lemma circleLift_product_flux_eventually (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i =ᶠ[𝓝 y]
    (fun w ↦ Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 w.2) * baseChartFlux A rho f p.1 j w.1)
      (fun _ ↦ 0) i) := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with w hw
  exact circleLift_actual_product_flux A rho hA hp hr hrp hrad f hf p hw i

lemma circleLift_product_flux_smooth_at (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    ContDiffAt ℝ ∞ (basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i) y := by
  have hs : ContDiffAt ℝ ∞
      (fun w : Model ↦ Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 w.2) *
        baseChartFlux A rho f p.1 j w.1) (fun _ ↦ 0) i) y := by
    cases i with
    | inl j =>
      exact ((circleChartDensity_smooth_at p.2 (product_chart_target p hy).2).comp y contDiffAt_snd).mul
        ((baseChartFlux_smooth_at A rho hA hp hr hrp f hf p.1 (product_chart_target p hy).1 j).comp y contDiffAt_fst)
    | inr j => exact contDiffAt_const
  exact hs.congr_of_eventuallyEq
    (circleLift_product_flux_eventually A rho hA hp hr hrp hrad f hf p hy i)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CircleLaplacian
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
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)
include hrad hf

lemma independentAmbientMetric_circle_laplacian (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
    (baseChartDensity rho p.1 y.1)⁻¹ * ∑ i,
      fderiv ℝ (baseChartFlux A rho f p.1 i) y.1 (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  rw [chartLaplacian_product_basis _ p _ (fun i ↦
    (circleLift_product_flux_smooth_at A rho hA hp hr hrp hrad f hf p hy i).differentiableAt (by simp))]
  unfold basisMetricLaplacian
  rw [basisMetricMatrix_product,independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy]
  have hd (i : Fin 4 ⊕ Fin 1) :=
    (circleLift_product_flux_eventually A rho hA hp hr hrp hrad f hf p hy i).fderiv_eq (𝕜 := ℝ)
  simp_rw [hd]
  exact separated_density_cancellation (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis (baseChartFlux A rho f p.1)
    (fun t ↦ Real.sqrt (circleChartFactor p.2 t)) (baseChartDensity rho p.1 y.1)
    (fun i ↦ (baseChartFlux_smooth_at A rho hA hp hr hrp f hf p.1
      (product_chart_target p hy).1 i).differentiableAt (by simp))
    ((circleChartDensity_smooth_at p.2 (product_chart_target p hy).2).differentiableAt (by simp))
    (Real.sqrt_pos.mpr (circleChartFactor_pos p.2 (product_chart_target p hy).2)).ne'

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_GlobalSphereEquation
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

omit hA hs hp hf in
lemma intrinsic_global_equation_at_center
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho f p z =
      lam*f ((extChartAt (𝓡 4) p).symm z)) :
    ∀ x : Base, -intrinsicWeightedChartOperator A rho f x (extChartAt (𝓡 4) x x) = lam*f x := by
  intro x
  simpa only [(extChartAt (𝓡 4) x).left_inv (mem_extChartAt_source x)] using he x (extChartAt (𝓡 4) x x)

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetShortCircleArc
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Jets
open scoped ContDiff Topology
noncomputable section

lemma productChartDomain_iff (p : Manifold5) (a b : ℝ) (z : _root_.OAI.Yau.Jets.Coord × ℝ) :
    z ∈ productChartDomain p a b ↔
      WithLp.toLp 2 z.1 ∈ (extChartAt (𝓡 4) p.1).target ∧
      WithLp.toLp 2 (fun _ : Fin 1 ↦ a+b*z.2) ∈ (extChartAt (𝓡 1) p.2).target := by
  have he : modelCoordinateEquiv.symm (z.1,a+b*z.2) =
      (WithLp.toLp 2 z.1, WithLp.toLp 2 (fun _ : Fin 1 ↦ a+b*z.2)) := rfl
  change modelCoordinateEquiv.symm (z.1,a+b*z.2) ∈
    (extChartAt modelWithCorners p).target ↔ _
  rw [he]
  simp [modelWithCorners]
  rfl

lemma exists_short_circle_arc (p : Manifold5) :
    ∃ a b : ℝ, 0 < b ∧ ∀ {K : Set _root_.OAI.Yau.Jets.Coord},
      (∀ y ∈ K, WithLp.toLp 2 y ∈ (extChartAt (𝓡 4) p.1).target) →
      K ×ˢ Icc (-1:ℝ) 1 ⊆ productChartDomain p a b := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 1 ↦ ℝ)
  let a := e (extChartAt (𝓡 1) p.2 p.2)
  let V := e.symm ⁻¹' (extChartAt (𝓡 1) p.2).target
  have hV : IsOpen V := (isOpen_extChartAt_target p.2).preimage e.symm.continuous
  have ha : a ∈ V := by simp [V,a]
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ha)
  refine ⟨a,r/2,by positivity,?_⟩
  intro K hK z hz
  rw [productChartDomain_iff]
  refine ⟨hK z.1 hz.1,?_⟩
  have habs : |z.2| ≤ 1 := abs_le.mpr hz.2
  have hin : a+(r/2)*z.2 ∈ V := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have hnorm : |a+(r/2)*z.2-a| = (r/2)*|z.2| := by
      rw [add_sub_cancel_left,abs_mul,abs_of_pos (by positivity : 0 < r/2)]
    rw [hnorm]
    nlinarith
  exact hin

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicPairUniformBounds
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

lemma intrinsic_sphere_upper_bound (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c > 0, ∀ x v, A x v v ≤ c*roundCotangentTensor x v v := by
  let B := fun x ↦ ambientMatrixForm (intrinsicAmbientMatrix A x)
  have hB : Continuous B := (ambientMatrixForm_smooth _ (intrinsicAmbientMatrix_smooth A hA)).continuous
  have hpos (x : Base) (v : AmbientBase) (hv : v ≠ 0) : 0 < B x v v :=
    ambientMatrixForm_pos _ (intrinsicAmbientMatrix_posDef A hs hp x) v hv
  have hc : Continuous (fun z : Base × AmbientBase ↦ B z.1 z.2 z.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨_,_,c,hc0,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:AmbientBase) 1)) _ hc.continuousOn
    (fun z hz ↦ hpos z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hb (x : Base) (v : AmbientBase) : B x v v ≤ c*‖v‖^2 := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (x,(‖v‖⁻¹:ℝ) • v)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).2
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

lemma intrinsic_pair_uniform_bounds (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, ∃ B > 0, ∃ R > 0,
      (∀ x v, c*roundCotangentTensor x v v ≤ A x v v) ∧
      (∀ x v, A x v v ≤ B*roundCotangentTensor x v v) ∧
      (∀ x, c ≤ rho x) ∧ (∀ x, rho x ≤ R) := by
  obtain ⟨c,hc,hlo,hrlo⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  obtain ⟨B,hB,hhi⟩ := intrinsic_sphere_upper_bound A hA hs hp
  obtain ⟨_,_,R,hR,hb⟩ := compact_positive_bounds isCompact_univ rho hr.continuous.continuousOn
    (fun x _ ↦ hrp x)
  exact ⟨c,hc,B,hB,R,hR,hlo,hhi,hrlo,fun x ↦ (hb x (mem_univ _)).2⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PerturbedNodalTransfer
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst7
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst8
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst9
local instance perturbedNodalTransferLocalInst1_ref6fe8_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst2_ref6fe8_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst3_ref6fe8_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst4_ref6fe8_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst5_ref6fe8_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance perturbedNodalTransferLocalInst6_ref6fe8_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance perturbedNodalTransferLocalInst10_ref6fe8_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.perturbedNodalTransferLocalInst11
local instance perturbedNodalTransferLocalInst12_ref6fe8_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance perturbedNodalTransferLocalInst13_ref6fe8_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance perturbedNodalTransferLocalInst14_ref6fe8_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance perturbedNodalTransferLocalInst15_ref6fe8_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance perturbedNodalTransferLocalInst16_ref6fe8_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
lemma circleLift_productChartInverse (f : Base → ℝ) (a b : ℝ) (q : Circle) (z : _root_.OAI.Yau.Jets.Coord × ℝ) :
    circleLift f (productChartInverse (seedPoint,q) a b z) = f (seedSphereFromCoord z.1) := by
  unfold circleLift productChartInverse
  rw [extChartAt_prod]
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_SphereFiniteNormNodalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal NNReal
noncomputable section

theorem sphere_finite_norm_uniform_nodal_transfer (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    {H : Set Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ eta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
        sphereCoefficientDistance P 0 d.tensor d.density b.tensor b.density < eta →
        ∀ (u : Base → ℝ) (U : Set Yau.Jets.Coord), U ⊆ H →
          Measure.hausdorffMeasure (4:ℝ)
            ((U ×ˢ Icc (-1:ℝ) 1) ∩ {z : Yau.Jets.Coord × ℝ | u (seedSphereFromCoord z.1)=0}) ≤
          (C:ℝ≥0∞)^4 * nodalMeasure
            (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive) (circleLift u) := by
  obtain ⟨c,hc,B,hB,R,hR,hlo,hhi,hrlo,hrhi⟩ :=
    intrinsic_pair_uniform_bounds d.tensor d.smooth d.symm d.pos d.density hd d.positive
  obtain ⟨eta,heta,Heta⟩ := sphere_coefficient_relative_form_comparison P hcover
    d.tensor d.smooth d.symm d.pos d.density hd d.positive (1/2) (by norm_num)
  obtain ⟨a,t,ht,hchart⟩ := exists_short_circle_arc (seedPoint,(1:Circle))
  obtain ⟨C,hC,htransfer⟩ := uniform_intrinsic_coefficient_nodal_transfer
    (c/2) (3*B/2) (c/2) (3*R/2) (by positivity) (by positivity) (by positivity) (by positivity)
    (seedPoint,(1:Circle)) a ht.ne' (hH.prod isCompact_Icc)
    (hchart (fun y hy ↦ by rw [centeredSphereChart_target]; trivial))
  refine ⟨eta,heta,C,hC,?_⟩
  intro b hb hdist u U hUH
  have hcmp := Heta b.tensor b.density b.smooth b.symm b.pos hb hdist
  have hblo : ∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫=0 →
      (c/2)*‖v‖^2 ≤ b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) := by
    intro x v hv
    have h := hlo x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at h
    have hh := abs_le.mp ((hcmp x).1 (sphereCovectorRestriction x v))
    nlinarith
  have hbhi : ∀ (x : Base) (v : AmbientBase), ⟪(x:AmbientBase),v⟫=0 →
      b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ (3*B/2)*‖v‖^2 := by
    intro x v hv
    have h := hhi x (sphereCovectorRestriction x v)
    rw [roundCotangentTensor_tangent x v v hv hv,real_inner_self_eq_norm_sq] at h
    have hh := abs_le.mp ((hcmp x).1 (sphereCovectorRestriction x v))
    nlinarith
  have hbrlo (x : Base) : c/2 ≤ b.density x := by
    have hh := abs_le.mp (hcmp x).2
    linarith [hrlo x]
  have hbrhi (x : Base) : b.density x ≤ 3*R/2 := by
    have hh := abs_le.mp (hcmp x).2
    linarith [hrhi x]
  apply htransfer b.tensor b.smooth b.symm b.pos b.density hb b.positive hblo hbhi hbrlo hbrhi
  · rintro z ⟨hz,_⟩
    exact ⟨hUH hz.1,hz.2⟩
  · rintro z ⟨_,hzero⟩
    rw [circleLift_productChartInverse]
    exact hzero

end
end Yau.Target

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
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_SphereReferenceNodalPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Set Yau.Geometry
open scoped ContDiff ENNReal NNReal
noncomputable section

theorem sphere_reference_literal_nodal_persistence_oai
    (P₀ : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P₀, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x)
    (d₀ : SphereEnergyData) (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density)
    {H : Set Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ delta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (d : SphereEnergyData), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density →
        sphereCoefficientDistance P₀ 0 d₀.tensor d₀.density d.tensor d.density < delta →
        ∀ (u : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → u ≠ 0 →
        ∀ lam > 0,
          (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
            lam*u ((extChartAt (𝓡 4) p).symm y)) →
          (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
            (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
              lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) →
          ∀ (g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
            (S : Yau.Jets.Coord → ℝ) (Q U : Set Yau.Jets.Coord) (n : ℕ) (M : ℝ),
            U ⊆ H → LiteralNodalCertificate g S Q U n (fun x ↦ u (seedSphereFromCoord x)) M →
            ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
              ∃ P : Finset Base, P₀ ⊆ P ∧
                ∃ eta > 0, ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
                  sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
                  sphereIndexedEigenvalue b N ∈ Icc (lam/2) (2*lam) ∧
                  ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
                    (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
                      sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) ∧
                    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
                    (∀ x : Manifold5, -chartLaplacian
                      (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                      (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
                        sphereIndexedEigenvalue b N*circleLift v x) ∧
                    ENNReal.ofReal (M/(C:ℝ)^4) ≤ nodalMeasure
                      (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive) (circleLift v) := by
  classical
  obtain ⟨delta,hdelta,C,hC,Htransfer⟩ := sphere_finite_norm_uniform_nodal_transfer P₀ hcover d₀ hd₀ hH
  refine ⟨delta/2,by positivity,C,hC,?_⟩
  intro d hd hdist₀ u hu hu0 lam hlam he hsimple g S Q U n M hUH hcert
  obtain ⟨eps,heps,Hcert⟩ := hcert.uniform_persistence
  obtain ⟨N,hN,P₁,hP₁,Hspec⟩ := sphere_finite_norm_simple_oriented_persistence d hd u hu hu0 lam hlam he hsimple
  obtain ⟨eta,heta,Heta⟩ := Hspec eps heps
  refine ⟨N,hN,P₀ ∪ P₁,Finset.subset_union_left,min eta (delta/2),lt_min heta (by positivity),?_⟩
  intro b hb hdist
  have hd₁ := (sphereCoefficientDistance_mono_atlas P₁ (P₀ ∪ P₁) Finset.subset_union_right d b hd hb 8).trans_lt
    (hdist.trans_le (min_le_left _ _))
  obtain ⟨hval,v,hv,hv0,hve,hclose⟩ := Heta b hb hd₁
  have hdb : sphereCoefficientDistance P₀ 0 d.tensor d.density b.tensor b.density < delta/2 :=
    (sphereCoefficientDistance_mono_order P₀ d b hd hb 0 8 (by omega)).trans_lt
      ((sphereCoefficientDistance_mono_atlas P₀ (P₀ ∪ P₁) Finset.subset_union_left d b hd hb 8).trans_lt
        (hdist.trans_le (min_le_right _ _)))
  have htriangle := sphereCoefficientDistance_triangle P₀ 0 d₀.tensor d.tensor b.tensor
    d₀.density d.density b.density
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d₀.tensor d₀.smooth d₀.symm d₀.pos d₀.density hd₀ p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p)
  have hnear : sphereCoefficientDistance P₀ 0 d₀.tensor d₀.density b.tensor b.density < delta := by linarith
  have hcoord := Hcert (fun x ↦ v (seedSphereFromCoord x))
    (hv.continuous.comp seedSphereFromCoord_continuous) (fun x ↦ hclose (seedSphereFromCoord x))
  have hmeasure := ofReal_le_of_fourth_power_mul_le hC (hcoord.trans (Htransfer b hb hnear v U hUH))
  have hlift := intrinsicWeightedMetric_eigenfunction b.tensor b.smooth b.symm b.pos b.density hb b.positive
    v hv hv0 (sphereIndexedEigenvalue b N)
    (intrinsic_global_equation_at_center b.tensor b.density v _ hve)
  exact ⟨hval,v,hv,hv0,hve,hlift.1,hlift.2.1,hlift.2.2,hmeasure⟩

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.sphere_reference_literal_nodal_persistence_oai := @OAI.Yau.Target.sphere_reference_literal_nodal_persistence_oai
