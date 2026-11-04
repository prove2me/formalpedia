-- Prove2me | solution 1 for ThreeSum.LocalKeyArraySemantics.meets_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:21.561046+00:00
-- url     : https://prove2.me/submissions/5c26d1d6-c2f8-460d-a9a3-62971eb332b1

import Definitions.Def_Submission_ThreeSum_OutputKeyMasks
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Theorems.Thm_ThreeSum_LocalKeyArraySemantics_seg_localKeys
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_le
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LocalMaskGraph_maskAt_spec


set_option autoImplicit false
open ThreeSum ThreeSum.LocalKeyArraySemantics
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open Light
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LocalKeyArraySemantics
theorem _root_.solution {pMain h masks maps dst free : ℕ} {μ : ℕ → ℤ}
    (S : LightLocalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free (512*h) (outputCount (512*h) h) ≤ lim.space)
    (hmasks : masks+outputCount (512*h) h ≤ dst)
    (hmaps : maps+scheduleSize h*(2*(512*h)) ≤ dst)
    (hdst : dst+scheduleSize h*outputCount (512*h) h ≤ free)
    (hword : (LightLocalKeys.word (512*h) (localPrime h) (scheduleSize h) : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < outputCount (512*h) h,
      μ (masks+i)=(LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ))
    (hreadFalse : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+i)=(BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < scheduleSize h, ∀ i < 512*h,
      μ (maps+j*(2*(512*h))+512*h+i)=(BlockCoefficientRows.mapRow h true j i : ℤ)) :
    Meets lim P pMain d [512*h,masks,outputCount (512*h) h,maps,scheduleSize h,dst,free] μ
      (LightLocalKeys.time (512*h) (outputCount (512*h) h) (scheduleSize h))
      (fun _ ν => Seg ν dst (localKeys h) ∧ Kept μ ν dst) := by
  apply (S.meets (U := localPrime h) (LocalMaskGraph.maskAt (512*h) (2*h))
    (BlockCoefficientRows.mapRow h false) (BlockCoefficientRows.mapRow h true)
    hw hd hspace hmasks hmaps hdst hword hmaskRead
    (fun i hi => (LocalMaskGraph.maskAt_spec hi).1) hreadFalse hreadTrue
    (fun j hj i hi => BlockCoefficientRows.mapRow_le false hj hi)
    (fun j hj i hi => BlockCoefficientRows.mapRow_le true hj hi)).mono le_rfl
  intro r ν ⟨hout,hkeep⟩
  exact ⟨seg_localKeys hout,hkeep⟩
end ThreeSum.LocalKeyArraySemantics
