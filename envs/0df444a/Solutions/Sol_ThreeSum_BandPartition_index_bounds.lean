-- Prove2me | solution 1 for ThreeSum.BandPartition.index_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:10.884407+00:00
-- url     : https://prove2.me/submissions/97eaa814-a53c-49d2-929f-43f506288735

import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_BandPartition

set_option autoImplicit false
open ThreeSum ThreeSum.BandPartition
namespace ThreeSum.BandPartition
theorem _root_.solution {n g i : ℕ} (hg : 0 < g) (hi : i < n) :
    start g (i/g) ≤ i ∧ i < stop n g (i/g) := by
  have hlo := Nat.div_mul_le_self i g
  have hmod := Nat.mod_lt i hg
  have hsum := Nat.mod_add_div i g
  unfold start stop
  constructor
  · exact hlo
  · have hh : i < (i/g+1)*g := by nlinarith
    omega
end ThreeSum.BandPartition
