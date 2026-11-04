-- Prove2me | solution 1 for ThreeSum.BlockSourceEncoding.key_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:30.697594+00:00
-- url     : https://prove2.me/submissions/63634e22-07c8-47a7-a2c6-af49533f778d

import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Theorems.Thm_ThreeSum_LightResidues_residue_cast
import Theorems.Thm_ThreeSum_LightSourceResidues_key_cast


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceEncoding
open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.BlockSourceEncoding
theorem _root_.solution {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    key p m shift x = LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, key_cast hm, LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]
end ThreeSum.BlockSourceEncoding
