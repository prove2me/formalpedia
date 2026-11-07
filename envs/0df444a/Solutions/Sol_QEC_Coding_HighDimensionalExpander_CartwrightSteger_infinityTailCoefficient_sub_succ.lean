-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityTailCoefficient_sub_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:27:43.420205+00:00
-- url     : https://prove2.me/submissions/441e7768-ea5d-47f9-81ed-5d4bd51fc41c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_infinityCyclicCoefficient
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_infinityCyclicCoefficient_succ
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCoefficientNat_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k i : ℕ) (ζ : ConstantExtension P r) :
    ζ * (constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r) -
        (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
          (constantFrobenius P r).symm
            ((constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u (i + 1) :
                ConstantExtension P r)) =
      infinityConjugationCoefficient P r u k ζ *
        (infinityCyclicCoefficient P r u (k + i) :
          ConstantExtension P r) := by
  rw [constantFrobenius_pow_infinityCyclicCoefficient]
  rw [constantFrobenius_symm_pow_infinityCyclicCoefficient_succ]
  rw [infinityCyclicCoefficient_coe]
  rw [← infinityConjugationCoefficientNat_eq]
  rw [infinityConjugationCoefficientNat, infinityCyclicInverseCoefficient]
  field_simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
