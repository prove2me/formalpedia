-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:14:47.595611+00:00
-- url     : https://prove2.me/submissions/ab78db1d-6495-429b-980f-7d62e5c2d40b

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Definitions.Def_WeightedCache3SUM_Alias_405ce37bf76953b6
import Definitions.Def_WeightedCache3SUM_Alias_188c0aebc110975b


set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace ThreeSum.LightCoverKeyData
theorem _root_.solution {lim : Limits} {μ : ℕ → ℤ} {h J free d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : LightCoverKeys.space free h J ≤ lim.space)
    (hword : (LightCoverKeys.word h J : ℤ) ≤ lim.word) :
    Meets lim LightCoverKeys.program 67 d [h,J,free] μ (LightCoverKeys.time h J)
      (fun r ν => r=(LightCoverKeys.keyHeader free h J : ℤ) ∧ Stored ν free h J ∧ Kept μ ν free) := by
  exact (LightCoverKeys.programProcs.meets_with_masks hw hd hspace hword).mono le_rfl
    (fun _ _ ⟨hr,hc,hk,hh,hd,hs,hi,hm,hkeep⟩ => ⟨hr,⟨hc,hk,hh,hd,hs,hi,hm⟩,hkeep⟩)
end ThreeSum.LightCoverKeyData
