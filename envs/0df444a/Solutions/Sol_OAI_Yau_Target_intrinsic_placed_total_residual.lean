-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_placed_total_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:03.310296+00:00
-- url     : https://prove2.me/submissions/1b7c96e5-6efa-44e6-beea-f9ff3d8929d9

import Mathlib
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
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_PlacedEnvelopeData_seeded_residual_of_seed_support

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma coordPartial_contDiff {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (coordPartial i f) :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end
end Yau.Jets

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

lemma roundChartDensity_pos (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) : 0 < roundChartDensity p z :=
  Real.sqrt_pos.mpr (sphereRoundChartMatrix_posDef p hz).det_pos

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CenteredSphereSecondJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma centeredSphereChart_frame_function (p : Base) :
    sphereChartDerivative p = fderiv ℝ
      (stereoInvFunAux (-(p : AmbientBase)) ∘ (centeredSphereIsometry p)) := by
  funext y
  rw [sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial),
    centeredSphereChart_inverse]

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ComplexMetricFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourcePrincipal_smooth_at
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (sourcePrincipal g i j) x := by
  have hi : ContDiffAt ℝ ∞ (fun z ↦ ContinuousLinearMap.inverse (g z)) x := by
    have h := contDiffAt_map_inverse (n := ∞) (positiveMetricEquiv (g x) hp)
    exact h.comp x hg.contDiffAt
  exact (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.contDiffAt.comp x
    (hi.clm_apply contDiffAt_const)

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CenteredRoundOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma sphereChartTensor_one (p : Base) (y : BaseModel) :
    sphereChartTensor (fun _ ↦ (1 : Matrix (Fin 5) (Fin 5) ℝ)) p y =
      (sphereRoundChartMatrix p y)⁻¹ := by
  unfold sphereChartTensor
  rw [sphereChart_contravariant _ PosDef.one (show (0:ℝ)<1 by norm_num) p
    (by rw [centeredSphereChart_target]; trivial) (by simp)]
  simp [sphereWeightedChartMatrix,Yau.Geometry.weightedBaseMatrix,sphereRoundChartMatrix]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FixedChartRoundOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundTensorFlux_conformal (f : Base → ℝ) (p : Base) (i : Fin 4) (y : BaseModel) :
    roundTensorFlux (fun _ ↦ 1) f p i y =
      (4/(‖y‖^2+4))^2 *
        fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) y (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  rw [roundTensorFlux,roundChartDensity_conformal,sphereChartTensor_one,
    sphereRoundChartMatrix_inverse_conformal]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  have hn : 4/(‖y‖^2+4) ≠ 0 := by positivity
  field_simp

lemma roundConformalSquare_hasFDerivAt (y : BaseModel) :
    HasFDerivAt (fun z : BaseModel ↦ (4/(‖z‖^2+4))^2)
      ((-64/(‖y‖^2+4)^3) • innerSL ℝ y) y := by
  have h := ((stereoReciprocal_hasFDerivAt y).const_mul 4).pow 2
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp [stereoReciprocal,smul_eq_mul,div_eq_mul_inv]
  field_simp
  ring

lemma roundTensorFlux_fixed_derivative (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (y : BaseModel) (i : Fin 4) :
    fderiv ℝ (roundTensorFlux (fun _ ↦ 1) f p i) y (EuclideanSpace.basisFun (Fin 4) ℝ i) =
      (-64/(‖y‖^2+4)^3)*y i *
        fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) y (EuclideanSpace.basisFun (Fin 4) ℝ i) +
      (4/(‖y‖^2+4))^2 *
        fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm)) y
          (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  have hd := ((smooth_inverse_chart_derivative f hf p
    (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.basisFun (Fin 4) ℝ i) y)
  have h := (roundConformalSquare_hasFDerivAt y).mul hd
  have he : roundTensorFlux (fun _ ↦ 1) f p i = fun z ↦ (4/(‖z‖^2+4))^2 *
      fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ i) :=
    funext (roundTensorFlux_conformal f p i)
  change HasFDerivAt (fun z ↦ (4/(‖z‖^2+4))^2 *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) _ y at h
  rw [he,h.fderiv]
  simp [EuclideanSpace.inner_single_right,smul_eq_mul]
  ring

theorem fixedChartRoundOperator (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (y : BaseModel) :
    ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) f p y =
      ((‖y‖^2+4)^2/16) *
        (∑ i, fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm)) y
          (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i)) -
      ((‖y‖^2+4)/4) *
        (∑ i, y i * fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) y
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
  simp only [ambientWeightedChartOperator,inv_one,one_mul,roundChartDensity_conformal,
    roundTensorFlux_fixed_derivative f hf,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  field_simp
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartTangentTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereConformalBasis_apply (p : Base) (y : BaseModel) (i : Fin 4 ⊕ Fin 1) :
    sphereConformalBasis p y i = sphereConformalFrame p y i := by
  simp [sphereConformalBasis]

lemma sphere_chart_tangent_trace (f : AmbientBase → ℝ) (p : Base) (y : BaseModel) :
    (∑ i, fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))) =
    (4/(‖y‖^2+4))^2 *
      (Δ f ((extChartAt (𝓡 4) p).symm y : AmbientBase) -
       fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase)) := by
  have h := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (sphereConformalBasis p y)) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
  simp only [Fintype.sum_sum_type,iteratedFDeriv_two_apply,sphereConformalBasis_apply,
    sphereConformalFrame,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one,map_smul,smul_apply,smul_eq_mul,
    Fin.sum_univ_one,← mul_assoc,← Finset.mul_sum] at h
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  rw [h]
  field_simp
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_StereographicArbitrarySecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereoInvFunAux_second_at (v x w u : E) :
    fderiv ℝ (fun z ↦ fderiv ℝ (stereoInvFunAux v) z w) x u =
      (8 * stereoReciprocal x^3 * ⟪x,u⟫ * ⟪x,w⟫ -
        2 * stereoReciprocal x^2 * ⟪u,w⟫) • stereoNumerator v x +
      (-2 * stereoReciprocal x^2 * ⟪x,w⟫) • ((4:ℝ) • u + (2*⟪x,u⟫) • v) +
      (-2 * stereoReciprocal x^2 * ⟪x,u⟫) • ((4:ℝ) • w + (2*⟪x,w⟫) • v) +
      (2 * stereoReciprocal x * ⟪u,w⟫) • v := by
  simp_rw [stereoInvFunAux_fderiv]
  have hb : HasFDerivAt (fun z : E ↦ ⟪z,w⟫) (innerSL ℝ w) x := by
    convert! (innerSL ℝ w).hasFDerivAt (x := x) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact (real_inner_comm z w).symm
  have hA := (((stereoReciprocal_hasFDerivAt x).pow 2).const_mul (-2:ℝ)).mul hb
  have hB := (hasFDerivAt_const ((4:ℝ) • w) x).add ((hb.const_mul (2:ℝ)).smul_const v)
  have hd := (hA.smul (stereoNumerator_hasFDerivAt v x)).add
    ((stereoReciprocal_hasFDerivAt x).smul hB)
  change HasFDerivAt (fun z : E ↦
    (-2 * stereoReciprocal z^2 * ⟪z,w⟫) • stereoNumerator v z +
      stereoReciprocal z • ((4:ℝ) • w + (2*⟪z,w⟫) • v)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul,
    Pi.mul_apply,Pi.add_apply,zero_add,real_inner_comm w u,show (2:ℕ)-1=1 from rfl,pow_one]
  module

lemma stereoInvFunAux_second_fderiv_at (v x w u : E) :
    fderiv ℝ (fderiv ℝ (stereoInvFunAux v)) x u w =
      fderiv ℝ (fun z ↦ fderiv ℝ (stereoInvFunAux v) z w) x u := by
  have hd := (contDiff_stereoInvFunAux (v := v) (m := ∞)).fderiv_right
    (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (hd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  simpa using (congrArg (fun L : E →L[ℝ] E ↦ L u) he.fderiv).symm

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereChartArbitrarySecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereChart_second_stereo (p : Base) (y u v : BaseModel) :
    fderiv ℝ (sphereChartDerivative p) y u v =
      fderiv ℝ (fun z ↦ fderiv ℝ (stereoInvFunAux (-(p:AmbientBase))) z
        (centeredSphereIsometry p v)) (centeredSphereIsometry p y)
        (centeredSphereIsometry p u) := by
  rw [centeredSphereChart_frame_function]
  have h := (centeredSphereIsometry p).toContinuousLinearMap.iteratedFDeriv_comp_right
    (contDiff_stereoInvFunAux (v := -(p : AmbientBase)) (m := ∞)) y
    (i := 2) (show (2:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have he := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ BaseModel) AmbientBase ↦
    D ![u,v]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  exact he.trans (stereoInvFunAux_second_fderiv_at _ _ _ _)

lemma sphereChart_second_at (p : Base) (y u v : BaseModel) :
    fderiv ℝ (sphereChartDerivative p) y u v =
      (-2/(‖y‖^2+4)) •
        (⟪y,u⟫ • sphereChartDerivative p y v +
         ⟪y,v⟫ • sphereChartDerivative p y u -
         ⟪u,v⟫ • sphereChartDerivative p y y) -
      ((4/(‖y‖^2+4))^2 * ⟪u,v⟫) •
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) := by
  have hF := congrFun (centeredSphereChart_inverse p) y
  simp only [Function.comp_apply] at hF
  rw [sphereChart_second_stereo,stereoInvFunAux_second_at,hF]
  simp only [sphereChartDerivative_stereo,stereoInvFunAux_fderiv,
    stereoReciprocal,stereoNumerator,stereoInvFunAux,
    (centeredSphereIsometry p).norm_map,(centeredSphereIsometry p).inner_map_map,real_inner_self_eq_norm_sq]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  ext i
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul]
  field_simp
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SphereRestrictionArbitraryHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereInverse_contDiff (p : Base) :
    ContDiff ℝ ∞ ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) := by
  rw [centeredSphereChart_inverse]
  exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry p).contDiff

lemma sphere_restriction_chart_first_at (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (y v : BaseModel) :
    fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm) y v =
      fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase) (sphereChartDerivative p y v) := by
  change fderiv ℝ (f ∘ ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm)) y v = _
  rw [fderiv_comp y (hf.differentiable (by simp) _)
    ((sphereInverse_contDiff p).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
    ← sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)]
  rfl

lemma smooth_comp_second_at {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F → G) (h : E → F) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ h)) x u v =
      fderiv ℝ (fderiv ℝ f) (h x) (fderiv ℝ h x u) (fderiv ℝ h x v) +
      fderiv ℝ f (h x) (fderiv ℝ (fderiv ℝ h) x u v) := by
  have hdf := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdh := (hh.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hG := (hdf (h x)).hasFDerivAt.comp x (hh.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt
  have hD := (hdh x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hd := hG.clm_apply hD
  have he : (fun z ↦ fderiv ℝ (f ∘ h) z v) =
      (fun z ↦ fderiv ℝ f (h z) (fderiv ℝ h z v)) := by
    funext z
    rw [fderiv_comp z (hf.differentiable (by simp) _) (hh.differentiable (by simp) _)]
    rfl
  have hQ := ((hf.comp hh).fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have hE := congrArg (fun L : E →L[ℝ] G ↦ L u)
    (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at hE
  change HasFDerivAt (fun z ↦ fderiv ℝ f (h z) (fderiv ℝ h z v)) _ x at hd
  rw [← hE,he,hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_zero,
    zero_add,ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma sphere_restriction_chart_second_at (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (y u v : BaseModel) :
    fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) y u v =
      fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        (sphereChartDerivative p y u) (sphereChartDerivative p y v) +
      fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        (fderiv ℝ (sphereChartDerivative p) y u v) := by
  let F : BaseModel → AmbientBase := (Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm
  have hFd : fderiv ℝ F = sphereChartDerivative p := by
    funext z
    exact (sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)).symm
  have h := smooth_comp_second_at f F hf (sphereInverse_contDiff p) y u v
  rw [hFd] at h
  exact h

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FixedChartAmbientLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphere_coordinate_linear_sum (L : BaseModel →L[ℝ] ℝ) (y : BaseModel) :
    ∑ i, y i * L (EuclideanSpace.basisFun (Fin 4) ℝ i) = L y := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr y)
  simpa using h

lemma sphere_restriction_second_trace_at (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (y : BaseModel) :
    (∑ i, fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) y
      (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
    (∑ i, fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
      (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))) +
    (4/(‖y‖^2+4)) *
      fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm) y y -
    (4*(4/(‖y‖^2+4))^2) *
      fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) := by
  simp only [sphere_restriction_chart_second_at f hf,sphereChart_second_at,
    map_sub,map_add,map_smul,smul_eq_mul]
  have hi (i : Fin 4) : ⟪y,EuclideanSpace.basisFun (Fin 4) ℝ i⟫ = y i := by
    rw [real_inner_comm,EuclideanSpace.basisFun_inner]
  simp only [(EuclideanSpace.basisFun (Fin 4) ℝ).inner_eq_ite,ite_true, if_true,hi,one_mul,mul_one]
  simp_rw [← sphere_restriction_chart_first_at f hf]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hs := sphere_coordinate_linear_sum
    (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm) y) y
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at *
  rw [hs]
  ring

local instance : Fact (Module.finrank ℝ AmbientBase = 4 + 1) := ⟨by simp [AmbientBase]⟩

theorem fixed_chart_round_operator_ambient_restriction (f : AmbientBase → ℝ)
    (hf : ContDiff ℝ ∞ f) (p : Base) (y : BaseModel) :
    ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (fun x : Base ↦ f x) p y =
      Δ f ((extChartAt (𝓡 4) p).symm y : AmbientBase) -
      fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) -
      4 * fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        ((extChartAt (𝓡 4) p).symm y : AmbientBase) := by
  have hfm : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x : Base ↦ f x) :=
    hf.contMDiff.comp (contMDiff_coe_sphere (n := 4))
  rw [fixedChartRoundOperator _ hfm,sphere_restriction_second_trace_at f hf,
    sphere_chart_tangent_trace,sphere_coordinate_linear_sum]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  field_simp
  ring

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r6c4a7b_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedZ1_apply (x : SeedAmbient) : seedZ1 x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := rfl
lemma seedZ2_apply (x : SeedAmbient) : seedZ2 x = (x 2 : ℂ) + Complex.I * (x 3 : ℂ) := rfl

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedPolynomialDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff
noncomputable section

lemma seedQuadratic_hasFDerivAt (x : SeedAmbient) :
    HasFDerivAt seedQuadratic (seedQuadraticDerivative x) x :=
  (seedZ1.hasFDerivAt).mul (seedZ2.hasFDerivAt)

lemma ambientComplexSeed_hasFDerivAt (N : ℕ) (x : SeedAmbient) :
    HasFDerivAt (ambientComplexSeed N)
      (((N:ℂ) * seedQuadratic x^(N-1)) • seedQuadraticDerivative x) x := by
  convert! (seedQuadratic_hasFDerivAt x).pow N using 1
  all_goals try with_reducible_and_instances rfl
  simp [nsmul_eq_mul]

lemma ambientComplexSeed_fderiv (N : ℕ) (x v : SeedAmbient) :
    fderiv ℝ (ambientComplexSeed N) x v =
      (N:ℂ) * seedQuadratic x^(N-1) *
        (seedZ1 x * seedZ2 v + seedZ2 x * seedZ1 v) := by
  rw [(ambientComplexSeed_hasFDerivAt N x).fderiv]
  rfl

lemma seedQuadraticDerivative_apply_hasFDerivAt (x v : SeedAmbient) :
    HasFDerivAt (fun y ↦ seedQuadraticDerivative y v)
      (seedZ2 v • seedZ1 + seedZ1 v • seedZ2) x := by
  convert! (seedZ1.hasFDerivAt.mul_const (seedZ2 v)).add
    (seedZ2.hasFDerivAt.mul_const (seedZ1 v)) using 1
  all_goals try with_reducible_and_instances rfl

lemma ambientComplexSeed_second (N : ℕ) (x v w : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientComplexSeed N) y v) x w =
      (N:ℂ) * ((N-1:ℕ):ℂ) * seedQuadratic x^(N-1-1) *
        seedQuadraticDerivative x w * seedQuadraticDerivative x v +
      (N:ℂ) * seedQuadratic x^(N-1) *
        (seedZ2 v * seedZ1 w + seedZ1 v * seedZ2 w) := by
  have he : (fun y ↦ fderiv ℝ (ambientComplexSeed N) y v) =
      (fun y ↦ (N:ℂ) * seedQuadratic y^(N-1) * seedQuadraticDerivative y v) := by
    funext y
    rw [(ambientComplexSeed_hasFDerivAt N y).fderiv]
    rfl
  rw [he]
  have hd := (((seedQuadratic_hasFDerivAt x).pow (N-1)).const_mul (N:ℂ)).mul
    (seedQuadraticDerivative_apply_hasFDerivAt x v)
  change HasFDerivAt (fun y ↦ (N:ℂ) * seedQuadratic y^(N-1) * seedQuadraticDerivative y v) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,nsmul_eq_mul]
  ring

lemma ambientRealSeed_fderiv (N : ℕ) (x v : SeedAmbient) :
    fderiv ℝ (ambientRealSeed N) x v = (fderiv ℝ (ambientComplexSeed N) x v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x (ambientComplexSeed_hasFDerivAt N x)
  change HasFDerivAt (ambientRealSeed N) _ x at h
  rw [h.fderiv,(ambientComplexSeed_hasFDerivAt N x).fderiv]
  rfl

lemma ambientRealSeed_second (N : ℕ) (x v w : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientRealSeed N) y v) x w =
      (fderiv ℝ (fun y ↦ fderiv ℝ (ambientComplexSeed N) y v) x w).re := by
  simp_rw [ambientRealSeed_fderiv]
  have hc := ((ambientComplexSeed_contDiff N).fderiv_right (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    (contDiff_const (c := v))
  exact congrArg (fun L : SeedAmbient →L[ℝ] ℝ ↦ L w)
    (Complex.reCLM.hasFDerivAt.comp x
      (hc.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt).fderiv

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedAmbientHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open scoped ContDiff
open Laplacian InnerProductSpace
noncomputable section

lemma seed_second_eq_iterated {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SeedAmbient → F) (hf : ContDiff ℝ ∞ f) (x v w : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w = iteratedFDeriv ℝ 2 f x ![w,v] := by
  have hd := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [h.fderiv,iteratedFDeriv_two_apply]
  simp

lemma seedZ1_basis (i : Fin 5) : seedZ1 (EuclideanSpace.basisFun (Fin 5) ℝ i) =
    if i = 0 then 1 else if i = 1 then Complex.I else 0 := by
  fin_cases i <;> simp [seedZ1_apply,EuclideanSpace.basisFun_apply]

lemma seedZ2_basis (i : Fin 5) : seedZ2 (EuclideanSpace.basisFun (Fin 5) ℝ i) =
    if i = 2 then 1 else if i = 3 then Complex.I else 0 := by
  fin_cases i <;> simp [seedZ2_apply,EuclideanSpace.basisFun_apply]

lemma seedQuadratic_isotropic (x : SeedAmbient) :
    ∑ i, (seedQuadraticDerivative x (EuclideanSpace.basisFun (Fin 5) ℝ i))^2 = 0 := by
  simp only [seedQuadraticDerivative,add_apply,smul_apply,smul_eq_mul]
  simp_rw [seedZ1_basis,seedZ2_basis]
  simp [Fin.sum_univ_succ,mul_pow,Complex.I_sq]

lemma seedQuadratic_trace :
    ∑ i, (seedZ2 (EuclideanSpace.basisFun (Fin 5) ℝ i) *
      seedZ1 (EuclideanSpace.basisFun (Fin 5) ℝ i) +
      seedZ1 (EuclideanSpace.basisFun (Fin 5) ℝ i) *
      seedZ2 (EuclideanSpace.basisFun (Fin 5) ℝ i)) = 0 := by
  simp_rw [seedZ1_basis,seedZ2_basis]
  simp [Fin.sum_univ_succ]

lemma ambientComplexSeed_laplacian (N : ℕ) : Δ (ambientComplexSeed N) = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 5) ℝ)]
  funext x
  simp_rw [← seed_second_eq_iterated _ (ambientComplexSeed_contDiff N),ambientComplexSeed_second]
  simp_rw [mul_assoc ((N:ℂ) * ((N-1:ℕ):ℂ) * seedQuadratic x^(N-1-1)),← pow_two]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    seedQuadratic_isotropic,seedQuadratic_trace]
  simp

lemma ambientRealSeed_laplacian (N : ℕ) : Δ (ambientRealSeed N) = 0 := by
  funext x
  have hc : ContDiffAt ℝ 2 (ambientComplexSeed N) x :=
    ((ambientComplexSeed_contDiff N).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
  change Δ (Complex.reCLM ∘ ambientComplexSeed N) x = 0
  rw [hc.laplacian_CLM_comp_left,ambientComplexSeed_laplacian]
  simp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRadialDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
noncomputable section

lemma seedQuadraticDerivative_radial (x : SeedAmbient) :
    seedQuadraticDerivative x x = 2 * seedQuadratic x := by
  simp only [seedQuadraticDerivative,add_apply,smul_apply,smul_eq_mul,seedQuadratic]
  ring

lemma ambientComplexSeed_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (ambientComplexSeed N) x x = (2*(N:ℂ))*ambientComplexSeed N x := by
  rw [ambientComplexSeed_fderiv]
  change (N:ℂ) * seedQuadratic x^(N-1) * seedQuadraticDerivative x x = _
  rw [seedQuadraticDerivative_radial]
  simp only [ambientComplexSeed]
  cases N with
  | zero => simp
  | succ n => simp only [Nat.succ_sub_one,Nat.cast_succ,pow_succ] <;> ring

lemma ambientComplexSeed_second_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientComplexSeed N) y x) x x =
      (2*(N:ℂ))*(2*(N:ℂ)-1)*ambientComplexSeed N x := by
  rw [ambientComplexSeed_second,seedQuadraticDerivative_radial]
  rw [show seedZ2 x * seedZ1 x + seedZ1 x * seedZ2 x = 2*seedQuadratic x by
    unfold seedQuadratic; ring]
  simp only [ambientComplexSeed]
  rcases N with _ | (_ | n)
  · simp
  · norm_num
  · simp only [Nat.succ_sub_one,Nat.cast_succ,pow_succ] <;> ring

lemma ambientRealSeed_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (ambientRealSeed N) x x = (2*(N:ℝ))*ambientRealSeed N x := by
  rw [ambientRealSeed_fderiv,ambientComplexSeed_radial]
  simp [ambientRealSeed,Complex.mul_re]

lemma ambientRealSeed_second_radial (N : ℕ) (x : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ (ambientRealSeed N) y x) x x =
      (2*(N:ℝ))*(2*(N:ℝ)-1)*ambientRealSeed N x := by
  rw [ambientRealSeed_second,ambientComplexSeed_second_radial]
  simp [ambientRealSeed,Complex.mul_re]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FixedChartSeedEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold InnerProductSpace Laplacian
open scoped ContDiff
noncomputable section

theorem sphericalSeed_fixed_chart_round_eigenfunction (N : ℕ) (p : Base) (y : BaseModel) :
    -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) (sphericalSeed N) p y =
      seedEigenvalue N * sphericalSeed N ((extChartAt (𝓡 4) p).symm y) := by
  change -ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1)
    (fun x : Base ↦ ambientRealSeed N x) p y = _
  rw [fixed_chart_round_operator_ambient_restriction _ (ambientRealSeed_contDiff N),
    ambientRealSeed_laplacian,ambientRealSeed_radial]
  have hd := ambientRealSeed_second_radial N ((extChartAt (𝓡 4) p).symm y : SeedAmbient)
  rw [seed_second_eq_iterated _ (ambientRealSeed_contDiff N),iteratedFDeriv_two_apply] at hd
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hd
  rw [hd]
  simp only [Pi.zero_apply,sphericalSeed,seedEigenvalue]
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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GlobalSeedResidualSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Set Filter
open scoped Topology
noncomputable section

lemma ambientWeightedChartOperator_coefficients_eq
    (A B : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho sigma : Base → ℝ)
    (f : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hA : A =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] B)
    (hr : rho =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] sigma) :
    ambientWeightedChartOperator A rho f p z = ambientWeightedChartOperator B sigma f p z := by
  have he := hA.comp_tendsto (continuousAt_extChartAt_symm'' hz)
  have hf (i : Fin 4) : roundTensorFlux A f p i =ᶠ[𝓝 z] roundTensorFlux B f p i := by
    filter_upwards [he] with y hy
    simp only [roundTensorFlux,sphereChartTensor,Function.comp_def] at *
    rw [hy]
  simp only [ambientWeightedChartOperator,hr.eq_of_nhds]
  congr 2
  funext i
  rw [(hf i).fderiv_eq]

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

lemma sourceHessian_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    sourceHessian g S =ᶠ[𝓝 x] sourceHessian G A := by
  filter_upwards [hg,hg.fderiv (𝕜 := ℝ),hS.fderiv (𝕜 := ℝ),
    (hS.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)] with z hz hd hs hss
  simp only [sourceHessian,hz,hd,hs,hss]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSmoothExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem compact_smooth_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  have hsupp : tsupport G ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [G,hz])
  refine ⟨G,hG,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_⟩
  intro x hx
  filter_upwards [hb1 x hx] with z hz
  simp [G,hz]

theorem compact_positive_metric_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ,
      ContDiff ℝ ∞ G ∧ (∀ x u v, G x u v = G x v u) ∧
      (∀ x v, v ≠ 0 → 0 < G x v v) ∧ ∀ x ∈ K, G =ᶠ[𝓝 x] g := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  obtain ⟨x0,hx0⟩ := hUn
  let G := fun x ↦ b x • g x + (1-b x) • g x0
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact (hb.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hbU hx)))).add
        ((contDiffAt_const.sub hb.contDiffAt).smul contDiffAt_const)
    · apply (contDiffAt_const (c := g x0)).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x u v
    by_cases hx : x ∈ tsupport b
    · change b x*g x u v+(1-b x)*g x0 u v = b x*g x v u+(1-b x)*g x0 v u
      rw [hs x (hbU hx),hs x0 hx0]
    · simp [G,image_eq_zero_of_notMem_tsupport hx,hs x0 hx0]
  · intro x v hv
    by_cases hx : x ∈ tsupport b
    · have h1 := hp x (hbU hx) v hv
      have h2 := hp x0 hx0 v hv
      have hb0 := (hbr x).1
      have hb1 := (hbr x).2
      change 0 < b x*g x v v+(1-b x)*g x0 v v
      by_cases hz : b x = 0
      · simpa [hz] using h2
      · have ha : 0 < b x := lt_of_le_of_ne hb0 (Ne.symm hz)
        have hleft := mul_pos ha h1
        have hright := mul_nonneg (sub_nonneg.mpr hb1) h2.le
        linarith
    · simpa [G,image_eq_zero_of_notMem_tsupport hx] using hp x0 hx0 v hv
  · intro x hx
    filter_upwards [hb1 x hx] with z hz
    simp [G,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSourceRepresentatives
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
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

theorem compact_source_representatives {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hS : ContDiffOn ℝ ∞ S U)
    (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (W A : _root_.OAI.Yau.Jets.Coord → ℝ) (E : Set _root_.OAI.Yau.Jets.Coord),
      ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ W ∧ ContDiff ℝ ∞ A ∧
      (∀ x u v, G x u v = G x v u) ∧ (∀ x v, v ≠ 0 → 0 < G x v v) ∧
      IsOpen E ∧ K ⊆ E ∧ E ⊆ U ∧ (∀ x ∈ E, 0 < W x) ∧
      ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) ∧
        metricGradient G A x = metricGradient g S x ∧ sourceHessian G A x = sourceHessian g S x := by
  obtain ⟨G,hG,hGs,hGp,hGe⟩ := compact_positive_metric_extension hK hU hKU hUn g hg hs hp
  obtain ⟨W,hW,_,_,hWe⟩ := compact_smooth_extension hK hU hKU w hw
  obtain ⟨A,hA,_,_,hAe⟩ := compact_smooth_extension hK hU hKU S hS
  let B : Set _root_.OAI.Yau.Jets.Coord := {x | G x = g x ∧ W x = w x ∧ A x = S x}
  let E := U ∩ interior B
  have hE : IsOpen E := hU.inter isOpen_interior
  have hKE : K ⊆ E := by
    intro x hx
    refine ⟨hKU hx,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact (hGe x hx).and ((hWe x hx).and (hAe x hx))
  have hgerm (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ E) : (G =ᶠ[𝓝 x] g) ∧
      (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) := by
    have hh : ∀ᶠ z in 𝓝 x, G z = g z ∧ W z = w z ∧ A z = S z :=
      mem_of_superset (hE.mem_nhds hx) (fun z hz ↦ interior_subset hz.2)
    exact ⟨hh.mono (fun _ h ↦ h.1),hh.mono (fun _ h ↦ h.2.1),hh.mono (fun _ h ↦ h.2.2)⟩
  refine ⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hKE,inter_subset_left,?_,?_⟩
  · intro x hx
    rw [(hgerm x hx).2.1.self_of_nhds]
    exact hwp x hx.1
  · intro x hx
    obtain ⟨heG,heW,heA⟩ := hgerm x hx
    exact ⟨heG,heW,heA,(metricGradient_eventuallyEq heG heA).self_of_nhds,
      (sourceHessian_eventuallyEq heG heA).self_of_nhds⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSourceOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
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

lemma smoothFluxOperator_smooth (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hv : ContDiff ℝ ∞ v) (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (smoothFluxOperator v F u) :=
  hv.mul (ContDiff.sum (fun i _ ↦ coordPartial_contDiff
    (ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))) i))

theorem compact_source_operator_coefficients {Q U : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ),
      ContDiff ℝ ∞ v ∧ (∀ i j, ContDiff ℝ ∞ (F i j)) ∧
      ∀ x ∈ Q, ∀ u : _root_.OAI.Yau.Jets.Coord → ℂ,
        sourceWeightedOperator g w u =ᶠ[𝓝 x] smoothFluxOperator v F u := by
  obtain ⟨G,W,A,E,hG,hW,_,hGs,hGp,hE,hQE,hEU,hWp,he⟩ :=
    compact_source_representatives hQ hU hQU hUn g hg hs hp w (fun _ ↦ 0) hw contDiffOn_const hwp
  have hWi : ContDiffOn ℝ ∞ (fun x ↦ (W x)⁻¹) E :=
    hW.contDiffOn.inv (fun x hx ↦ ne_of_gt (hWp x hx))
  obtain ⟨V,hV,_,_,hVe⟩ := compact_smooth_extension hQ hE hQE _ hWi
  let F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ := fun i j x ↦ (W x:ℂ)*(sourcePrincipal G i j x:ℂ)
  have hF (i j : Fin 4) : ContDiff ℝ ∞ (F i j) := by
    have ha : ContDiff ℝ ∞ (sourcePrincipal G i j) :=
      contDiff_iff_contDiffAt.mpr (fun x ↦ sourcePrincipal_smooth_at G hG x (hGp x) i j)
    exact (Complex.ofRealCLM.contDiff.comp hW).mul (Complex.ofRealCLM.contDiff.comp ha)
  refine ⟨fun x ↦ (V x:ℂ),F,Complex.ofRealCLM.contDiff.comp hV,hF,?_⟩
  intro x hx u
  have hcoef := sourceOperator_coefficients_eventuallyEq (he x (hQE hx)).1.symm
    (he x (hQE hx)).2.1.symm u
  filter_upwards [hcoef,hVe x hx] with z hz hvz
  rw [hz]
  simp only [smoothFluxOperator,sourceWeightedOperator,complexDivergence,F,hvz,
    Complex.ofReal_inv]
  rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_OperatorAddition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceOperator_smoothAt {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (sourceWeightedOperator g w u) x := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients (isCompact_singleton (x := x))
    hU (singleton_subset_iff.mpr hx) ⟨x,hx⟩ g hg hs hp w hw hwp
  exact (smoothFluxOperator_smooth v F hv hF u hu).contDiffAt.congr_of_eventuallyEq
    (he x (mem_singleton x) u)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SeededResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma realSourceResidual_smoothAt {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u : _root_.OAI.Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (realSourceResidual g w lam u) x :=
  (sourceOperator_smoothAt hU g hg hs hp w hw hwp _ (Complex.ofRealCLM.contDiff.comp hu) hx).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.comp hu).contDiffAt)

end
end Yau.Geometry

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

lemma seedCoordWeight_pos (rho : Base → ℝ) (hr : ∀ p, 0 < rho p) (x : _root_.OAI.Yau.Jets.Coord) :
    0 < seedCoordWeight rho x := by
  apply mul_pos (hr _)
  exact roundChartDensity_pos seedPoint (by rw [centeredSphereChart_target]; trivial)

lemma seedCoordWeight_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) : ContDiff ℝ ∞ (seedCoordWeight rho) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hz : seedCoordEquiv x ∈ (extChartAt (𝓡 4) seedPoint).target := by
    rw [centeredSphereChart_target]; trivial
  exact ((smooth_inverse_chart_comp rho hr seedPoint hz).mul
    (roundChartDensity_smooth_at seedPoint hz)).comp x seedCoordEquiv.contDiff.contDiffAt

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

lemma seedCoordinateField_literal (N : ℕ) (x : _root_.OAI.Yau.Jets.Coord) :
    seedCoordinateField N x = sphericalSeed N
      ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) := rfl

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

lemma intrinsicSeedCoord_residual (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x) (N : ℕ) (x : _root_.OAI.Yau.Jets.Coord) :
    sourceWeightedOperator (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (fun z ↦ (seedCoordinateField N z:ℂ)) x+
        (seedEigenvalue N:ℂ)*(seedCoordinateField N x:ℂ) =
      (intrinsicWeightedChartOperator A rho (sphericalSeed N) seedPoint (seedCoordEquiv x)+
        seedEigenvalue N*sphericalSeed N
          ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ) := by
  have he : seedCoordinateField N = fun z ↦ sphericalSeed N
      ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z)) := funext (seedCoordinateField_literal N)
  rw [he,intrinsicSeedCoordOperator A hA hs hp rho hrp _ (sphericalSeed_smooth N)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FixedChartSeedSupport
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Set Filter Yau.Geometry Yau.Jets
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section

lemma ambient_seed_fixed_chart_residual_zero
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    {K : Set Base} (hK : IsClosed K)
    (hA : ∀ p ∉ K, A p = 1) (hr : ∀ p ∉ K, rho p = 1)
    (N : ℕ) (p : Base) (y : BaseModel) (hy : (extChartAt (𝓡 4) p).symm y ∉ K) :
    ambientWeightedChartOperator A rho (sphericalSeed N) p y +
      seedEigenvalue N*sphericalSeed N ((extChartAt (𝓡 4) p).symm y) = 0 := by
  have hAe : A =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm y)] (fun _ ↦ 1) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with q hq
    exact hA q hq
  have hre : rho =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm y)] (fun _ ↦ 1) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with q hq
    exact hr q hq
  rw [ambientWeightedChartOperator_coefficients_eq A (fun _ ↦ 1) rho (fun _ ↦ 1)
    (sphericalSeed N) p (by rw [centeredSphereChart_target]; trivial) hAe hre]
  linarith [sphericalSeed_fixed_chart_round_eigenfunction N p y]

theorem intrinsicSeedCoord_residual_tsupport
    (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    {K : Set Base} (hK : IsClosed K)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (N : ℕ) :
    tsupport (realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (seedEigenvalue N) (seedCoordinateField N)) ⊆
      (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) ⁻¹' K := by
  have hc : Continuous (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) :=
    seedSphereChart_inverse_continuous.comp seedCoordEquiv.continuous
  apply closure_minimal _ (hK.preimage hc)
  intro x hx
  by_contra hxK
  apply hx
  rw [realSourceResidual,intrinsicSeedCoord_residual A hAs hs hp rho hrp,
    intrinsicWeightedChartOperator_eq]
  exact_mod_cast ambient_seed_fixed_chart_residual_zero (intrinsicAmbientMatrix A) rho hK
    (fun z hz ↦ intrinsicAmbientMatrix_reference A z (hA z hz)) hr N seedPoint
      (seedCoordEquiv x) hxK

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedDeviationCoordinates
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Geometry Yau.Jets
open scoped Topology
noncomputable section

lemma seedDeviationCoordinates_eq_image {K : Set Base}
    (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    seedDeviationCoordinates K =
      (fun p ↦ seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p)) '' K := by
  ext x
  constructor
  · intro hx
    refine ⟨(extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x),hx,?_⟩
    dsimp only
    rw [(extChartAt (𝓡 4) seedPoint).right_inv
      (by rw [centeredSphereChart_target]; trivial),seedCoordEquiv.symm_apply_apply]
  · rintro ⟨p,hp,rfl⟩
    change (extChartAt (𝓡 4) seedPoint).symm
      (seedCoordEquiv (seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p))) ∈ K
    rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv (hK hp)]
    exact hp

lemma seedDeviationCoordinates_compact {K : Set Base} (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    IsCompact (seedDeviationCoordinates K) := by
  rw [seedDeviationCoordinates_eq_image hchart]
  exact hK.image_of_continuousOn (seedCoordEquiv.symm.continuous.comp_continuousOn
    ((continuousOn_extChartAt seedPoint).mono hchart))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicTotalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section

theorem intrinsic_placed_total_residual_oai
    (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrs : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)
    {r a : ℝ} {K : Set Base} {T : ℝ}
    (d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T)
    (ha : 0 ≤ a) (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set _root_.OAI.Yau.Jets.Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∀ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n)
            ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ (R u) ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (coeff ∈ coefficientEvent (n:ℝ) → ∀ x : _root_.OAI.Yau.Jets.Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) := by
  have hreg := intrinsicSeedCoordMetric_regular A hAs hs hp rho hrs hrp
  have hweight := seedCoordWeight_smooth rho hrs
  have hweightp := seedCoordWeight_pos rho hrp
  have hsupport (n : ℕ) : tsupport
      (realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
        (seedEigenvalue n) (seedCoordinateField n)) ⊆ seedDeviationCoordinates K :=
    intrinsicSeedCoord_residual_tsupport A hAs hs hp rho hrp hK.isClosed hA hr n
  obtain ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hbound⟩ :=
    d.seeded_residual_of_seed_support ha (seedDeviationCoordinates_compact hK hchart)
      hreg.1.contDiffOn (fun x _ ↦ hreg.2.1 x) (fun x _ ↦ hreg.2.2 x)
      (seedCoordWeight rho) hweight.contDiffOn (fun x _ ↦ hweightp x) hsupport k0 K'
  refine ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hbound] with n hn
  obtain ⟨hfin,hn⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  have h := hn coeff
  refine ⟨h.1,?_,h.2⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact realSourceResidual_smoothAt isOpen_univ _ hreg.1.contDiffOn
    (fun x _ ↦ hreg.2.1 x) (fun x _ ↦ hreg.2.2 x)
    _ hweight.contDiffOn (fun x _ ↦ hweightp x) _ _ h.1 (mem_univ x)

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_placed_total_residual_oai := @OAI.Yau.Target.intrinsic_placed_total_residual_oai
