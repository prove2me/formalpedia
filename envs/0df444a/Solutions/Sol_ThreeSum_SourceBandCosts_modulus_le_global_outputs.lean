-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.modulus_le_global_outputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:01.787267+00:00
-- url     : https://prove2.me/submissions/dfd5f84f-4e5f-4d32-a50c-677971188795

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_choose_pow_le
import Theorems.Thm_ThreeSum_SourceBandCosts_four_le_scheduleSize
import Theorems.Thm_ThreeSum_SourceBandCosts_localPrime_le_four_outputs

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (h J : ℕ) :
    BlockSourceEncoding.modulus h J ≤ GlobalEncoding.scheduleSize h^J*
      (J*(512*h)).choose (J*(2*h)) := by
  have hl : localPrime h ≤ GlobalEncoding.scheduleSize h*outputCount (512*h) h :=
    (localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (choose_pow_le (512*h) (2*h) J))
end ThreeSum.SourceBandCosts
