-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.Represents.keep_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:10.834039+00:00
-- url     : https://prove2.me/submissions/e6b2b944-b8a4-4ea6-9db7-19a5e5bd23f3

import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPreprocessing
namespace Represents
theorem _root_.solution {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (h : Represents μ values endpoints g hg original L hs) (hk : Kept μ μ' bound)
    (hv : values+original.length ≤ bound) (he : endpoints+2+2*original.length ≤ bound) :
    Represents μ' values endpoints g hg original L hs := by
  obtain ⟨hseg,hn,hmem,hlen,hcount,hAt⟩ := h
  have hm := size_le L.length g
  refine ⟨?_,hn,hmem,?_,?_,?_⟩
  · intro i hi
    rw [hk (values+i) (by omega)]
    exact hseg i hi
  · rw [hk endpoints (by omega)]
    exact hlen
  · rw [hk (endpoints+1) (by omega)]
    exact hcount
  · exact hAt.keep hk (by change endpoints+2+size L.length g ≤ bound; omega)
      (by change endpoints+2+L.length+size L.length g ≤ bound; omega)
end Represents
end ThreeSum.LightBandPreprocessing
