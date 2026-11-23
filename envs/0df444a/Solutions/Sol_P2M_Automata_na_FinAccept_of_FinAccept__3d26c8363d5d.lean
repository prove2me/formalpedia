-- Prove2me | solution 1 for P2M_Automata_na_FinAccept_of_FinAccept__3d26c8363d5d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:54.868652+00:00
-- url     : https://prove2.me/submissions/a60e35eb-3c09-4c1d-95d8-b33770ff8a98

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Theorems.Thm_P2M_Automata_na_FinRun_of_FinRun__1438a22cbb33

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Inhabited A] {n : ℕ} {as : Fin n → A}
    (h : M.FinAccept' acc n as) : M.FinAccept acc n (fun k ↦ if h : k < n then as ⟨k, h⟩ else default) := by
  rcases h with ⟨ss, h_run, h_n⟩
  use (fun k ↦ if h : k < n + 1 then ss ⟨k, h⟩ else ss 0)
  constructor
  · exact na_FinRun_of_FinRun' h_run
  simpa
end Automata
