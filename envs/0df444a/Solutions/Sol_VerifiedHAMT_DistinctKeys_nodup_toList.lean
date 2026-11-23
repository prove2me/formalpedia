-- Prove2me | solution 1 for VerifiedHAMT.DistinctKeys.nodup_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:00.689177+00:00
-- url     : https://prove2.me/submissions/31087f87-1d77-4e40-aa22-f0e36e67bae1

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
public import Theorems.Thm_VerifiedHAMT_keyList_collision
attribute [local simp] VerifiedHAMT.keyList_collision

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
namespace DistinctKeys
theorem _root_.solution {keys : Array α} (h : DistinctKeys keys) :
    keys.toList.Nodup := by
  simp only [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [Array.length_toList] at hi hj
  have := h i hi j hj (by simpa using heq)
  omega
end DistinctKeys
end VerifiedHAMT
