-- Prove2me | solution 1 for ThreeSum.LightCoverKeys.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:14:48.928335+00:00
-- url     : https://prove2.me/submissions/184f250e-4099-4729-b19a-0ede8ae8c39b

import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_WeightedCache3SUM_Alias_405ce37bf76953b6
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Definitions.Def_WeightedCache3SUM_Alias_188c0aebc110975b


set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverKeys
namespace Procs
theorem _root_.solution {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,J,free] μ (time h J)
      (fun r ν => r=(keyHeader free h J : ℤ) ∧
        ν (keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        Seg ν (keyHeader free h J+1) (globalKeys h J) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps (LightLocalCoverInit.base free) h)
          (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
          (matrixPtr (LightLocalCoverInit.base free) h) ∧
        ScheduleRows ν h (scheduleMaps (LightLocalCoverInit.base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (LightLocalCoverInit.base free) h+s.val)=
          (candidateAt h s : ℤ)) ∧ Kept μ ν free) := by
  exact (S.meets_with_masks hw hd hspace hword).mono le_rfl
    (fun _ _ ⟨hr,hc,hkeys,hheader,hdata,hrows,hindices,_,hkeep⟩ =>
      ⟨hr,hc,hkeys,hheader,hdata,hrows,hindices,hkeep⟩)
end Procs
end ThreeSum.LightCoverKeys
