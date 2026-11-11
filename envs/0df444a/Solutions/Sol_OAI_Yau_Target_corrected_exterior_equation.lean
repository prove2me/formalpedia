-- Prove2me | solution 1 for OAI.Yau.Target.corrected_exterior_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:01.542916+00:00
-- url     : https://prove2.me/submissions/96cf9378-d39f-4086-b210-57944d7a0996

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
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
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_reb0a86_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedZ1_apply (x : SeedAmbient) : seedZ1 x = (x 0 : ℂ) + Complex.I * (x 1 : ℂ) := rfl
lemma seedZ2_apply (x : SeedAmbient) : seedZ2 x = (x 2 : ℂ) + Complex.I * (x 3 : ℂ) := rfl

lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

lemma ambientComplexSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientComplexSeed N) :=
  seedQuadratic_contDiff.pow N

lemma ambientRealSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientRealSeed N) :=
  Complex.reCLM.contDiff.comp (ambientComplexSeed_contDiff N)

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FixedChartSeedSupport
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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ExteriorCorrectedEquation
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

local instance exteriorCorrectedEquationLocalInst1_reb0a86_1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst2_reb0a86_1 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst3_reb0a86_1 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst4_reb0a86_1 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance exteriorCorrectedEquationLocalInst5_reb0a86_1 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance exteriorCorrectedEquationLocalInst6_reb0a86_1 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst7
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst8
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst9
local instance exteriorCorrectedEquationLocalInst10_reb0a86_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
attribute [local instance] OAI.Yau.Target.exteriorCorrectedEquationLocalInst11
local instance exteriorCorrectedEquationLocalInst12_reb0a86_1 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance exteriorCorrectedEquationLocalInst13_reb0a86_1 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance exteriorCorrectedEquationLocalInst14_reb0a86_1 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)
local instance exteriorCorrectedEquationLocalInst15_reb0a86_1 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance exteriorCorrectedEquationLocalInst16_reb0a86_1 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
lemma ambientWeightedChartOperator_field_eq (A : Base → Matrix (Fin 5) (Fin 5) ℝ)
    (rho : Base → ℝ) (u v : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (he : u =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] v) :
    ambientWeightedChartOperator A rho u p z = ambientWeightedChartOperator A rho v p z := by
  have he' := he.comp_tendsto (continuousAt_extChartAt_symm'' hz)
  have hder := he'.fderiv (𝕜 := ℝ)
  have hflux (i : Fin 4) : roundTensorFlux A u p i =ᶠ[𝓝 z] roundTensorFlux A v p i := by
    filter_upwards [hder] with y hy
    simp only [roundTensorFlux]
    rw [hy]
  unfold ambientWeightedChartOperator
  congr 2
  funext i
  rw [(hflux i).fderiv_eq]

theorem corrected_exterior_equation_oai (A : IntrinsicTensor) (rho : Base → ℝ)
    {K L : Set Base} (hK : IsClosed K) (hL : IsClosed L)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (a b u : Base → ℝ) (n : ℕ)
    (ha : tsupport a ⊆ L) (hb : tsupport b ⊆ L) (hu : tsupport (u-sphericalSeed n) ⊆ L)
    (p : Base) (z : BaseModel) (hz : (extChartAt (𝓡 4) p).symm z ∉ K ∪ L) :
    -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation a x)
      (fun x ↦ rho x+b x) u p z = seedEigenvalue n*u ((extChartAt (𝓡 4) p).symm z) := by
  have hAe (x : Base) (hx : x ∉ K ∪ L) :
      intrinsicAmbientMatrix (fun y ↦ A y+roundTensorPerturbation a y) x = 1 := by
    apply intrinsicAmbientMatrix_reference
    intro v w hv hw
    have hax : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Or.inr (ha h)))
    change A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)+
      a x*roundCotangentTensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = _
    rw [hax,zero_mul,add_zero]
    exact hA x (fun h ↦ hx (Or.inl h)) v w hv hw
  have hre (x : Base) (hx : x ∉ K ∪ L) : rho x+b x = 1 := by
    rw [hr x (fun h ↦ hx (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Or.inr (hb h))),add_zero]
  have hgerm : u =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] sphericalSeed n := by
    have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (Or.inr (hu h)))
    filter_upwards [hzero] with y hy
    exact sub_eq_zero.mp hy
  have he := ambient_seed_fixed_chart_residual_zero
    (intrinsicAmbientMatrix (fun x ↦ A x+roundTensorPerturbation a x)) (fun x ↦ rho x+b x)
    (hK.union hL) hAe hre n p z hz
  rw [intrinsicWeightedChartOperator_eq,
    ambientWeightedChartOperator_field_eq _ _ u (sphericalSeed n) p
      (by rw [centeredSphereChart_target]; trivial) hgerm,hgerm.eq_of_nhds]
  linarith

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.corrected_exterior_equation_oai := @OAI.Yau.Target.corrected_exterior_equation_oai
