-- Prove2me | solution 1 for ThreeSum.CyclicFold.mod_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:04.648386+00:00
-- url     : https://prove2.me/submissions/44d1b679-3360-4e02-ae39-7f1f9a9db3bf

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_Submission_ThreeSum_CyclicFold

set_option autoImplicit false
open ThreeSum ThreeSum.CyclicFold
open Finset Polynomial Karatsuba
open scoped BigOperators
namespace ThreeSum.CyclicFold
theorem _root_.solution {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p)
    (w : ℤ) :
    (if i + j = r then w else 0) + (if i + j = r + p then w else 0) =
      if (i + j) % p = r then w else 0 := by
  by_cases hsum : i + j < p
  · rw [Nat.mod_eq_of_lt hsum]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega
end ThreeSum.CyclicFold
