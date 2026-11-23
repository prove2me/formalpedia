-- Prove2me | solution 1 for automaton_congr_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:07.0163+00:00
-- url     : https://prove2.me/submissions/0d009194-63da-4514-9b3b-03e33b02d520

import Definitions.Def_AutomataTheory_Congruences_Basic
import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_Congr
import Theorems.Thm_P2M_Stream__extract_eq_nil_7f26d60de260
import Theorems.Thm_P2M_Stream__extract_succ_right__dce2e16ca09b


set_option autoImplicit true
open Function Set Stream'
attribute [local instance_reducible] Stream' Congruence.QuotType
variable {A : Type}
attribute [local instance_reducible] Congruence.toDA
variable {c : Congruence A}
theorem _root_.solution (as : Stream' A) (n : ℕ) :
    c.toDA.DetRun as n = ⟦ as.extract 0 n ⟧ := by
  induction' n with n h_ind
  · simp +instances [Automata.DA.DetRun, Congruence.toDA, extract_eq_nil]
  simp +instances only [Automata.DA.DetRun, h_ind]
  simp +instances only [Congruence.toDA, Quotient.lift_mk]
  simp +instances [extract_succ_right']
