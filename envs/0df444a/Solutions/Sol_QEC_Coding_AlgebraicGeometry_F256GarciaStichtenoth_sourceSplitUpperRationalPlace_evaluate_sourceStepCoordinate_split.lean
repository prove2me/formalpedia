-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:56.654038+00:00
-- url     : https://prove2.me/submissions/361e9d5d-9734-487c-92b9-7fe57457b457

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue
section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem sourceStepRhs_ne_zero_of_galoisBaseWValue_ne_zero
    (a : F256) (ha : galoisBaseWValue a ≠ 0) :
    sourceStepRhs a ≠ 0 := by
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply ha
    rw [galoisBaseWValue_eq, hzero]
    norm_num
  have hden : a ^ 15 + 1 ≠ 0 := by
    intro hzero
    apply ha
    rw [galoisBaseWValue_eq]
    calc
      a ^ 16 + a = a * (a ^ 15 + 1) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  rw [sourceStepRhs]
  exact div_ne_zero (pow_ne_zero 16 ha_ne) hden
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
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    galoisBaseWValue
        ((sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
          (sourceStepCoordinate P x hx)
          (sourceSplitAbovePlace_sourceStepCoordinate_regular
            Q P x hx hregular hsplit c)) ≠ 0 := by
  rw [sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue]
  exact sourceStepRhs_ne_zero_of_galoisBaseWValue_ne_zero
    (Q.evaluateRegular x hregular) hsplit
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
