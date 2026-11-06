-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_splitUpperPrime_auxiliary_mem_of_evaluate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:01.24614+00:00
-- url     : https://prove2.me/submissions/c4b7ce23-2b9f-4898-8a68-75744fc7159c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_splitUpperIdeal_auxiliary_residue_root
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_mem_f256ArtinSchreierRoots
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hzero : Q.evaluateRegular x hregular = 0) :
    ∃ c : LinearMap.ker f256ArtinSchreier,
      splitIntegralAuxiliaryCoordinate Q P x hx hregular ∈
        (splitUpperPrime Q P x hx c).1 := by
  letI : (splitBaseUpperIdeal Q P x hx).IsMaximal :=
    splitBaseUpperIdeal_isMaximal Q P x hx
  letI : (splitBaseUpperIdeal Q P x hx).LiesOver
      (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    splitBaseUpperIdeal_liesOver Q P x hx
  obtain ⟨b, hb, hroot⟩ :=
    exists_splitUpperIdeal_auxiliary_residue_root
      Q P x hx hregular (splitBaseUpperIdeal Q P x hx)
  have hbKernel : f256ArtinSchreier b = 0 := by
    rw [f256ArtinSchreier_apply]
    have hbEquation := (mem_f256ArtinSchreierRoots
      (Q.evaluateRegular x hregular) b).mp hb
    rw [hzero] at hbEquation
    simpa only [zero_pow (by norm_num : (17 : ℕ) ≠ 0)] using hbEquation
  let c : LinearMap.ker f256ArtinSchreier := ⟨b, hbKernel⟩
  have htranslated := translated_auxiliary_residue_mem_splitUpperPrime
    Q P x hx hregular b hroot c
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk, add_sub_cancel_right] using htranslated
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
