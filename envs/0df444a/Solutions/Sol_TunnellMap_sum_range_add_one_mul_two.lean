-- Prove2me | solution 1 for TunnellMap.sum_range_add_one_mul_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:31.761962+00:00
-- url     : https://prove2.me/submissions/da5915c9-2958-475b-9d1b-7b49e2c9bb14

import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_ParkingTotal
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (m : ℕ) :
    (Finset.sum (Finset.range m) fun i => i + 1) * 2 = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_mul, ih]
      ring
end TunnellMap
