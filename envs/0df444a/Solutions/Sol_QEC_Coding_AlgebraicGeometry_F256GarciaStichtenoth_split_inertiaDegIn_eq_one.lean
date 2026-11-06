-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.split_inertiaDegIn_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:08.766187+00:00
-- url     : https://prove2.me/submissions/569197ab-6afa-4157-ba24-952e064513c9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem split_ramificationIdxIn_mul_inertiaDegIn_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
          (SplitIntegralClosure Q P x hx) *
        (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
          (SplitIntegralClosure Q P x hx) = 1 := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  have hfundamental :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      m S G
  rw [split_primesOver_ncard Q P x hx hregular,
    stepField_algEquiv_card P x hx] at hfundamental
  have hcancel :
      16 * (m.ramificationIdxIn S * m.inertiaDegIn S) = 16 * 1 := by
    simpa only [Nat.mul_one] using hfundamental
  exact Nat.mul_left_cancel (by norm_num : 0 < 16) hcancel
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDegIn
      (SplitIntegralClosure Q P x hx) = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal Q.place.valuationRing).ramificationIdxIn
      (SplitIntegralClosure Q P x hx), ?_⟩
  simpa only [Nat.mul_comm] using
    (split_ramificationIdxIn_mul_inertiaDegIn_eq_one
      Q P x hx hregular).symm
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
