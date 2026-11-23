-- Prove2me | solution 1 for P2M_Automata_na_FinRun_of_FinRun__1438a22cbb33
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:09.115511+00:00
-- url     : https://prove2.me/submissions/6627a842-4f96-46a7-a755-34307f3c2f1b

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Inhabited A] {n : ℕ} {as : Fin n → A} {ss : Fin (n + 1) → M.State}
    (h : M.FinRun' n as ss) : M.FinRun n (fun k ↦ if h : k < n then as ⟨k, h⟩ else default)
      (fun k ↦ if h : k < n + 1 then ss ⟨k, h⟩ else ss 0) := by
  constructor
  · simp ; exact h.1
  intro k h_k
  have h_step := h.2 ⟨k, h_k⟩
  simp at h_step
  simpa [h_k, (show k < n + 1 by omega)]
end Automata
