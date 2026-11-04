-- Prove2me | solution 1 for ThreeSum.LightGlobalKeys.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:29.39034+00:00
-- url     : https://prove2.me/submissions/00ab4bfe-9c61-4d27-84cc-80db8a7acab4

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Definitions.Def_WeightedCache3SUM_Alias_188c0aebc110975b
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono


set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalKeys
namespace Procs
theorem _root_.solution {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+5 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ free)
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,2*h,scheduleSize h,localPrime h,J,maps,
      outputCount (512*h) h,free] μ (time h J)
      (fun r ν => r=((scratch free h+LightRadixKeys.offset (localCount h) J : ℕ) : ℤ) ∧
        ν (scratch free h+LightRadixKeys.offset (localCount h) J)=((localCount h^J : ℕ) : ℤ) ∧
        Seg ν (scratch free h+LightRadixKeys.offset (localCount h) J+1) (globalKeys h J) ∧
        Kept μ ν free) := by
  exact (S.meets_with_masks hw hd hspace hword hmaps hreadFalse hreadTrue).mono le_rfl
    (fun _ _ ⟨hr,hc,hg,_,hk⟩ => ⟨hr,hc,hg,hk⟩)
end Procs
end ThreeSum.LightGlobalKeys
