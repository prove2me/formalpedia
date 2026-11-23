-- Prove2me | solution 1 for VerifiedHAMT.contains_eq_false_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:28:23.07193+00:00
-- url     : https://prove2.me/submissions/f8062df1-bb0f-4aba-ad15-3f78beff26ca

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
public import Theorems.Thm_VerifiedHAMT_contains_eq_true_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}
namespace VerifiedHAMT
theorem _root_.solution [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = false ↔ ¬ Mem key map := by
  rw [← contains_eq_true_iff map wf key]
  cases contains map key <;> simp
end VerifiedHAMT
