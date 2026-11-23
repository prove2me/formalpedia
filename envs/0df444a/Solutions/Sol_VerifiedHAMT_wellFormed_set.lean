-- Prove2me | solution 1 for VerifiedHAMT.wellFormed_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:10.800813+00:00
-- url     : https://prove2.me/submissions/90b593df-6f35-46a5-9e55-0a742a34112f

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
theorem _root_.solution {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by
  cases wf with
  | entries size_eq routing children =>
    apply WellFormed.entries (by simpa using size_eq) <;> grind
end VerifiedHAMT
