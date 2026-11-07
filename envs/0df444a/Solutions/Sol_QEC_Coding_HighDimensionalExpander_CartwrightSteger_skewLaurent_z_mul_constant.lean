-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_z_mul_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:51.501754+00:00
-- url     : https://prove2.me/submissions/cafcb0bf-c265-44c0-a357-f56fbd216205

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_one_action_eq_frobenius
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 *
        SkewMonoidAlgebra.single 1 c =
      SkewMonoidAlgebra.single 1 (constantFrobenius P r c) *
        SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 := by
  rw [SkewMonoidAlgebra.single_mul_single,
    SkewMonoidAlgebra.single_mul_single]
  simp [one_action_eq_frobenius]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
