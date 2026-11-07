-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.le_sixtyFour_mul_nthRoot_six_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:42.564568+00:00
-- url     : https://prove2.me/submissions/ff684ab9-35b7-4b5c-afff-f167b254b837

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (n : Nat) (hn : 0 < n) :
    n ≤ 64 * (Nat.nthRoot 6 n) ^ 6 := by
  let x := Nat.nthRoot 6 n
  have hxPositive : 0 < x := by
    have hxOne : 1 ≤ Nat.nthRoot 6 n := by
      rw [Nat.le_nthRoot_iff (by norm_num)]
      simpa using (show 1 ≤ n by omega)
    exact hxOne
  have hnUpper : n < (x + 1) ^ 6 := by
    simpa [x] using Nat.lt_pow_nthRoot_add_one (by norm_num : 6 ≠ 0) n
  have hxDouble : x + 1 ≤ 2 * x := by omega
  calc
    n ≤ (x + 1) ^ 6 := hnUpper.le
    _ ≤ (2 * x) ^ 6 := Nat.pow_le_pow_left hxDouble 6
    _ = 64 * x ^ 6 := by ring
end QEC.Coding.TannerLiftedProduct
