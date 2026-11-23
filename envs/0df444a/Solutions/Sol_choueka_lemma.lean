-- Prove2me | solution 1 for choueka_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:54:11.274105+00:00
-- url     : https://prove2.me/submissions/4374ef1a-d1da-49d4-bf14-93d7a9cb987d

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_Automata_choueka_lang_omega_power_eq_omega_limit
import Theorems.Thm_Automata_choueka_lang_regular
import Theorems.Thm_reg_lang_det_accept
import Theorems.Thm_reg_lang_iter


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : ∃ L' : Set (List A), RegLang L' ∧ L^ω = L∗  * L'↗ω := by
  obtain ⟨M, acc, h_fin, h_lang⟩ := reg_lang_det_accept <| reg_lang_iter h
  use (M.ChouekaLang acc) ; constructor
  · apply Automata.choueka_lang_regular
  · apply Automata.choueka_lang_omega_power_eq_omega_limit h_lang.symm
