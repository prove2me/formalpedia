-- Prove2me | solution 1 for P2M_Automata_na_AcceptedLang_of_FinAccept__52bfd9b970d5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:29.073453+00:00
-- url     : https://prove2.me/submissions/a55945ce-4cdb-4b6f-b8f1-951e146f74bc

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Theorems.Thm_P2M_Automata_na_FinAccept__of_FinAccept_fdb8c514268d
import Theorems.Thm_P2M_Automata_na_FinAccept_of_FinAccept__3d26c8363d5d
import Theorems.Thm_P2M_Stream__extract_eq_ofFn_8231fd1645c4


set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Inhabited A] :
    M.AcceptedLang acc = { al | ∃ n as, M.FinAccept' acc n as ∧ List.ofFn as = al } := by
  rw [NA.AcceptedLang, Set.ext_iff] ; intro al ; constructor
  · rintro ⟨n, as, h_acc, rfl⟩
    use n, (fun k : Fin n ↦ as k)
    constructor
    · exact na_FinAccept'_of_FinAccept h_acc
    · simp [extract_eq_ofFn]
  · rintro ⟨n, as, h_acc, h_al⟩
    use n, (fun k ↦ if h : k < n then as ⟨k, h⟩ else default)
    constructor
    · exact na_FinAccept_of_FinAccept' h_acc
    · exact (Stream'.extract_eq_ofFn
        (xs := fun k ↦ if h : k < n then as ⟨k, h⟩ else default)
        (m := 0) (n := n)).trans (by simpa using h_al)
end Automata
