-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_zero_of_compactIdentityDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:22:36.5632+00:00
-- url     : https://prove2.me/submissions/baf25e54-7d63-42b2-8ae5-97d24d18d012

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_zero_of_constantFrobenius_pow_eq_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_eq_one_of_compactIdentityDiagonal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ) (j : ℕ)
    (hj : j < r.matrixRank)
    (hdiag : CompactNormalFormHasIdentityDiagonal P r u j) :
    j = 0 :=
  eq_zero_of_constantFrobenius_pow_eq_one P r j hj
    (constantFrobenius_pow_eq_one_of_compactIdentityDiagonal P r u j hdiag)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
