-- Prove2me | solution 1 for acc_lang_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:32.030844+00:00
-- url     : https://prove2.me/submissions/4a953a40-b875-4337-9d61-6c852357818f

import Definitions.Def_AutomataTheory_Congruences_Basic
import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_Congr
import Theorems.Thm_automaton_congr_run
import Theorems.Thm_Automata_da_fin_run_exists
import Theorems.Thm_Automata_da_fin_run_unique
import Theorems.Thm_P2M_Stream__extract_padDefault_dee05ba3940c


set_option autoImplicit true
open Function Set Stream'
attribute [local instance_reducible] Stream' Congruence.QuotType
variable {A : Type}
attribute [local instance_reducible] Congruence.toDA
variable {c : Congruence A}
theorem _root_.solution [Inhabited A] (s : c.toDA.State) :
    c.toDA.toNA.AcceptedLang {s} = c.EqvCls s := by
  ext al ; simp +instances [Automata.NA.AcceptedLang, Automata.NA.FinAccept] ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, rfl⟩, rfl⟩
    have h_ss_n := Automata.da_fin_run_unique h_run n (by omega)
    simp +instances [h_ss_n, automaton_congr_run, Congruence.EqvCls]
  · rintro ⟨rfl⟩
    use al.length, al.padDefault ; simp +instances [extract_padDefault]
    use (c.toDA.DetRun al.padDefault) ; constructor
    · exact Automata.da_fin_run_exists al.length al.padDefault
    · simp +instances [automaton_congr_run, extract_padDefault]
      exact Set.mem_singleton _
