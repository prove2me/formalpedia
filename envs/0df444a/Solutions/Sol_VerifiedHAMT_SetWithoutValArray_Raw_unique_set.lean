-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.unique_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:46.586066+00:00
-- url     : https://prove2.me/submissions/862a8eb7-f4fc-402e-8970-e58967a412eb

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution {es : Array (Entry α (Node α))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α (Node α)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by
  cases hu with
  | entries children => apply Unique.entries <;> grind
end VerifiedHAMT.SetWithoutValArray.Raw
