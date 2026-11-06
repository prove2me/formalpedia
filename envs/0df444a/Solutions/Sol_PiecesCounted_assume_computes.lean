-- Prove2me | solution 1 for PiecesCounted.assume_computes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:09.753875+00:00
-- url     : https://prove2.me/submissions/3af53a36-164f-4fd4-9243-3e762bb3e9b0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Trimmed
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Assume
import Theorems.Thm_PiecesCounted_ite_cast_min
import Theorems.Thm_GeneralPieces_Trim_length_bitsOf
import Theorems.Thm_GeneralPieces_Trim_length_rep
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_P2M_PiecesCounted_Data_Is_size_answer_le__00a9eaedb293
import Theorems.Thm_P2M_PiecesCounted_Data_Is_size_question_le__c8f9744f479a
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_PiecesCounted_assumeAlg_runs_one
import Theorems.Thm_PiecesCounted_assumeAlg_runs_two
import Theorems.Thm_PiecesCounted_bitsOf_toBits
import Theorems.Thm_PiecesCounted_four_steps_le
import Theorems.Thm_PiecesCounted_oracle_cap
import Theorems.Thm_PiecesCounted_oracle_eq_some
import Theorems.Thm_PiecesCounted_oracle_fn
import Theorems.Thm_PiecesCounted_oracle_value
import Theorems.Thm_PiecesCounted_room_eq
import Theorems.Thm_PiecesCounted_trimmed_cap
import Theorems.Thm_PiecesCounted_trimmed_fn_col
import Theorems.Thm_PiecesCounted_trimmed_fn_first
import Theorems.Thm_PiecesCounted_trimmed_fn_of_le
import Theorems.Thm_PiecesCounted_trimmed_fn_row
import Theorems.Thm_PiecesCounted_trimmed_is
import Theorems.Thm_PiecesCounted_two_room_le
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_close_bind
import Theorems.Thm_QueryMachines_QueryMachine_close_both
import Theorems.Thm_QueryMachines_QueryMachine_close_branch
import Theorems.Thm_QueryMachines_QueryMachine_close_const
import Theorems.Thm_QueryMachines_QueryMachine_close_foldRange
import Theorems.Thm_QueryMachines_QueryMachine_close_foldWhile
import Theorems.Thm_QueryMachines_QueryMachine_close_gated
import Theorems.Thm_QueryMachines_QueryMachine_close_ite
import Theorems.Thm_QueryMachines_QueryMachine_close_lift
import Theorems.Thm_QueryMachines_QueryMachine_close_mapAsk
import Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
import Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
import Theorems.Thm_QueryMachines_QueryMachine_close_optBind
import Theorems.Thm_QueryMachines_QueryMachine_close_prodRange
import Theorems.Thm_QueryMachines_QueryMachine_close_query
import Theorems.Thm_QueryMachines_QueryMachine_close_subst
import Theorems.Thm_QueryMachines_QueryMachine_close_sumRange
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] GeneralPieces.Trim.length_bitsOf
attribute [local simp] GeneralPieces.Trim.length_rep
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.TM.update_withIO
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit
attribute [local simp] QueryMachines.QueryMachine.close_bind
attribute [local simp] QueryMachines.QueryMachine.close_both
attribute [local simp] QueryMachines.QueryMachine.close_branch
attribute [local simp] QueryMachines.QueryMachine.close_const
attribute [local simp] QueryMachines.QueryMachine.close_foldRange
attribute [local simp] QueryMachines.QueryMachine.close_foldWhile
attribute [local simp] QueryMachines.QueryMachine.close_gated
attribute [local simp] QueryMachines.QueryMachine.close_ite
attribute [local simp] QueryMachines.QueryMachine.close_lift
attribute [local simp] QueryMachines.QueryMachine.close_mapAsk
attribute [local simp] QueryMachines.QueryMachine.close_mapIn
attribute [local simp] QueryMachines.QueryMachine.close_mapOut
attribute [local simp] QueryMachines.QueryMachine.close_optBind
attribute [local simp] QueryMachines.QueryMachine.close_prodRange
attribute [local simp] QueryMachines.QueryMachine.close_query
attribute [local simp] QueryMachines.QueryMachine.close_subst
attribute [local simp] QueryMachines.QueryMachine.close_sumRange



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {D : Data} {ρ : ℝ} {c : ℕ} {Alg : Stepped (List Unit × Question) Answer} (hD : D.Is ρ c) (hC : Computes Alg D c) : Computes (assumeAlg Alg) (trimmed D) (c + 2) := by
  intro g a hg
  obtain ⟨hl, ha⟩ := oracle_eq_some hg
  have s1 := (trimmed_is hD).size_question_le' hg
  have s2 := (trimmed_is hD).size_answer_le' hg
  have b1 := four_steps_le c hl
  have b2 := two_room_le hD.c_pos hl
  have b3 := room_eq c g.1.length
  have b4 : 1 ≤ steps c g.1.length := Nat.one_le_two_pow
  have one : ∀ a₀, Alg.Runs (firstQ g) (steps c g.1.length) (room c g.1.length) a₀ → afterFirst (g, a₀) = .inl a → (assumeAlg Alg).Runs g (steps (c + 2) g.1.length) (room (c + 2) g.1.length) a :=
    fun a₀ h1 h2 => (assumeAlg_runs_one h1 h2).mono (by omega) (by omega)
  have two : ∀ a₀ g', Alg.Runs (firstQ g) (steps c g.1.length) (room c g.1.length) a₀ → afterFirst (g, a₀) = .inr g' → Alg.Runs g' (steps c g.1.length) (room c g.1.length) a →
      (assumeAlg Alg).Runs g (steps (c + 2) g.1.length) (room (c + 2) g.1.length) a :=
    fun a₀ g' h1 h2 h3 => (assumeAlg_runs_two h1 h2 h3).mono (by omega) (by omega)
  clear s1 s2 b1 b2 b3 b4
  obtain ⟨u, q⟩ := g
  dsimp only at hl ha one two ⊢
  rcases q with q | q | q | q | q
  · exact one a (hC _ a hg) rfl
  · exact one a (hC _ a hg) rfl
  · obtain ⟨tr, i⟩ := q
    simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      have hi' : i ∈ (D.fam u.length).I := hi
      have ea : a = .inl ((trimmed D).cap u.length tr i : ℤ) := (Option.some.inj ha).symm
      subst ea
      have e : afterFirst ((u, .inr (.inr (.inl (tr, i)))), .inl (D.cap u.length tr i : ℤ)) = .inl (.inl ((trimmed D).cap u.length tr i : ℤ)) := by
        rw [trimmed_cap, ← ite_cast_min]
        rfl
      exact one _ (hC _ _ (oracle_cap hl hi' tr)) e
    · cases ha
  · exact one a (hC _ a hg) rfl
  · obtain ⟨⟨tr, side⟩, i, l1, l2, θ⟩ := q
    simp only [Data.answer] at ha
    split at ha
    · rename_i hi
      have ea : a = .inl ((trimmed D).fn u.length tr side i (toBits _ l1, toBits _ l2) θ) := (Option.some.inj ha).symm
      obtain ⟨hi, e1, e2, e3⟩ := hi
      have hi' : i ∈ (D.fam u.length).I := hi
      have e1' : l1.length = u.length := e1
      have e2' : l2.length = u.length := e2
      have e3' : θ.length = min (D.cap u.length tr i) (2 * u.length) := e3.trans (trimmed_cap D _ _ _)
      have r1 := hC _ _ (oracle_cap hl hi' tr)
      by_cases hc : D.cap u.length tr i ≤ 2 * u.length
      · rw [min_eq_left hc] at e3'
        have hp : ((D.cap u.length tr i : ℕ) : ℤ) ≤ ((2 * u.length : ℕ) : ℤ) := by exact_mod_cast hc
        have e : afterFirst ((u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))), .inl (D.cap u.length tr i : ℤ)) = .inr (u, .inr (.inr (.inr (.inr ((tr, side), i, l1, l2, θ))))) :=
          if_pos hp
        rw [trimmed_fn_of_le hc] at ea
        subst ea
        exact two _ _ r1 e (hC _ _ (oracle_fn hl hi' side e1' e2' e3'))
      · rw [min_eq_right (by omega)] at e3'
        have hn : ¬ ((D.cap u.length tr i : ℕ) : ℤ) ≤ ((2 * u.length : ℕ) : ℤ) := by exact_mod_cast hc
        have t1 : (θ.take u.length).length = u.length := by rw [List.length_take]; omega
        have t2 : (θ.drop u.length).length = u.length := by rw [List.length_drop]; omega
        cases side
        · have e : afterFirst ((u, .inr (.inr (.inr (.inr ((tr, false), i, l1, l2, θ))))), .inl (D.cap u.length tr i : ℤ)) = .inl (.inl (if l1 ++ l2 = θ then 1 else 0)) := if_neg hn
          rw [trimmed_fn_first hc, bitsOf_toBits e1', bitsOf_toBits e2'] at ea
          subst ea
          exact one _ r1 e
        · cases tr
          · have e : afterFirst ((u, .inr (.inr (.inr (.inr ((false, true), i, l1, l2, θ))))), .inl (D.cap u.length false i : ℤ)) =
                .inr (u, .inr (.inr (.inr (.inl (i, θ.take u.length, θ.drop u.length, l1, l2))))) := if_neg hn
            rw [trimmed_fn_row hc] at ea
            subst ea
            exact two _ _ r1 e (hC _ _ (oracle_value hl hi' t1 t2 e1' e2'))
          · have e : afterFirst ((u, .inr (.inr (.inr (.inr ((true, true), i, l1, l2, θ))))), .inl (D.cap u.length true i : ℤ)) =
                .inr (u, .inr (.inr (.inr (.inl (i, θ.take u.length, l1, θ.drop u.length, l2))))) := if_neg hn
            rw [trimmed_fn_col hc] at ea
            subst ea
            exact two _ _ r1 e (hC _ _ (oracle_value hl hi' t1 e1' t2 e2'))
    · cases ha
end PiecesCounted
