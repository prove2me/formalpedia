-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.unique_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:52:39.468024+00:00
-- url     : https://prove2.me/submissions/f335bba2-eb70-4215-983e-32d72b6ed34f

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_InsertProofs
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Unique
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_insertNode_unique

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
open Lean.PersistentHashMap (shift maxDepth)
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (set : Raw α) (wf : Valid set) (hu : Unique set.root) (key : α) :
    Unique (insert set key).root := by
  have bound : (0 : USize).toNat + 5 * (maxDepth.toNat - 1) ≤ 30 := by
    rcases System.Platform.numBits_eq with hb | hb <;> simp [maxDepth, USize.toNat_ofNat, hb]
  simpa [insert] using insertNode_unique (maxDepth.toNat - 1) 0 bound set.root
    (by simpa [Valid] using wf) hu key
end VerifiedHAMT.SetWithoutValArray.Raw
