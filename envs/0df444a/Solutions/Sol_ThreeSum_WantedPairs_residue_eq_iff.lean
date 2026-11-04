-- Prove2me | solution 1 for ThreeSum.WantedPairs.residue_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:32.23482+00:00
-- url     : https://prove2.me/submissions/2422d9a3-4180-431a-9d66-4d7a0b2f35ca

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_LightResidues_residue_cast


set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    LightResidues.residue M 1 b=LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),LightResidues.residue_cast hM,
    LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd
end ThreeSum.WantedPairs
