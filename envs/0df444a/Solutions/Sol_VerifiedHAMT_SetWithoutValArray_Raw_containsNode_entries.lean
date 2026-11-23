-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.containsNode_entries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:45:36.544606+00:00
-- url     : https://prove2.me/submissions/e8889cdc-d4dd-4963-99a0-ad6eeb781b9f

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Contains

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] (es : Array (Entry α (Node α)))
    (hash : USize) (key : α) :
    containsNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => false
        | .entry key' => key == key'
        | .ref child => containsNode child (nextHash hash) key
      else false := by
  rw [containsNode]
  split
  · split <;> simp_all
  · rfl
end VerifiedHAMT.SetWithoutValArray.Raw
