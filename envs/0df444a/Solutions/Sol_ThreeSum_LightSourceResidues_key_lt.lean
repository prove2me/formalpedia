-- Prove2me | solution 1 for ThreeSum.LightSourceResidues.key_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:17.244533+00:00
-- url     : https://prove2.me/submissions/1767282d-d181-4be5-bac3-0ea2c103dd6a

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Theorems.Thm_ThreeSum_LightSourceResidues_key_cast

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceResidues
theorem _root_.solution {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← key_cast hm] at h
  exact_mod_cast h
end ThreeSum.LightSourceResidues
