-- Prove2me | solution 1 for P2M_Automata_na_FinRun__of_FinRun_8f693dc0996c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:06.146667+00:00
-- url     : https://prove2.me/submissions/8233fac0-3e6d-4635-b53b-70d2dd33bf62

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.FinRun n as ss) : M.FinRun' n (fun k ↦ as k) (fun k ↦ ss k) := by
  constructor
  · simp ; exact h.1
  rintro ⟨k, h_k⟩
  simp
  exact h.2 k h_k
end Automata
