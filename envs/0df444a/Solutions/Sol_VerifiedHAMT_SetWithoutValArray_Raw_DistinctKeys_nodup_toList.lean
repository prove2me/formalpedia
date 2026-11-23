-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.DistinctKeys.nodup_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:44.351592+00:00
-- url     : https://prove2.me/submissions/df646f61-5b74-4fbd-85fc-cd1637be034e

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_keyList_collision
attribute [local simp] VerifiedHAMT.SetWithoutValArray.Raw.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
namespace DistinctKeys
theorem _root_.solution {keys : Array α} (h : DistinctKeys keys) :
    keys.toList.Nodup := by
  simp only [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [Array.length_toList] at hi hj
  have := h i hi j hj (by simpa using heq)
  omega
end DistinctKeys
end VerifiedHAMT.SetWithoutValArray.Raw
