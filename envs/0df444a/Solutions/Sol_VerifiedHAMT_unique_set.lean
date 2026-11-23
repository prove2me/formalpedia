-- Prove2me | solution 1 for VerifiedHAMT.unique_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:16.833354+00:00
-- url     : https://prove2.me/submissions/043e7f57-c557-4718-9193-769ff1968c12

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Bindings

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution {es : Array (Entry α β (Node α β))}
    (hu : Unique (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β)) (child : ∀ n, e = .ref n → Unique n) :
    Unique (.entries (es.set i e)) := by
  cases hu with
  | entries children => apply Unique.entries <;> grind
end VerifiedHAMT
