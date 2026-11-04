-- Prove2me | solution 1 for ThreeSum.LightSortedBands.Prepared.transfer_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:29.979619+00:00
-- url     : https://prove2.me/submissions/fb666f0a-4b06-4ed1-84de-2952a9a6a722

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_ThreeSum_BandPartition_size_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSortedBands
namespace Prepared
theorem _root_.solution {μ μ' : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original)
    (hk : ∀ a, (values ≤ a ∧ a < values+original.length) ∨
      (endpoints ≤ a ∧ a < endpoints+2+2*original.length) → μ' a = μ a) :
    Prepared μ' values endpoints g original := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  refine ⟨L,?_,hs,hn,hmem,?_,?_,?_,?_⟩
  · intro i hi
    rw [hk (values+i) (Or.inl (by omega))]
    exact hL i hi
  · rw [hk endpoints (Or.inr (by omega))]
    exact hlen
  · rw [hk (endpoints+1) (Or.inr (by omega))]
    exact hcount
  · intro i hi
    have hm := size_le L.length g
    rw [hk (endpoints+2+i) (Or.inr (by omega))]
    exact hlo i hi
  · intro i hi
    have hm := size_le L.length g
    rw [hk (endpoints+2+L.length+i) (Or.inr (by omega))]
    exact hhi i hi
end Prepared
end ThreeSum.LightSortedBands
