-- Prove2me | solution 1 for ThreeSum.LightBandRawAColor.tables_keep_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:29.472704+00:00
-- url     : https://prove2.me/submissions/9daa176e-a477-4342-b962-13368fb63625

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Theorems.Thm_ThreeSum_BandCandidateRows_index_lt
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
namespace ThreeSum.LightBandRawAColor
theorem _root_.solution {μ ν : ℕ → ℤ} {tables bound : ℕ} {A B C : BandEnumeration.Family}
    (ht : LightBandEnumeration.Tables μ tables A B C) (hk : Kept μ ν bound)
    (hb : tables+LightBandEnumeration.count A.size B.size C.size ≤ bound) :
    LightBandEnumeration.Tables ν tables A B C := by
  unfold LightBandEnumeration.count at hb
  refine ⟨?_,?_,?_⟩
  · intro j hj k hk'
    have hindex := index_lt hj hk'
    rw [hk _ (by omega)]
    exact ht.1 j hj k hk'
  · intro i hi j hj
    have hindex := index_lt hi hj
    rw [hk _ (by omega)]
    exact ht.2.1 i hi j hj
  · intro i hi k hk'
    have hindex := index_lt hi hk'
    rw [hk _ (by omega)]
    exact ht.2.2 i hi k hk'
end ThreeSum.LightBandRawAColor
