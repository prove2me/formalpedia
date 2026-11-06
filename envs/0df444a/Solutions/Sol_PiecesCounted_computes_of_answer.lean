-- Prove2me | solution 1 for PiecesCounted.computes_of_answer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:07.727199+00:00
-- url     : https://prove2.me/submissions/d0b2e859-c631-4b94-9089-88d48c4d0ec0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Padded
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_P2M_PiecesCounted_Data_Is_size_answer_le__00a9eaedb293
import Theorems.Thm_P2M_PiecesCounted_Data_Is_size_question_le__c8f9744f479a
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_PiecesCounted_oracle_eq_some
import Theorems.Thm_PiecesCounted_padThen_runs
import Theorems.Thm_PiecesCounted_room_eq
import Theorems.Thm_PiecesCounted_room_le_of_le
import Theorems.Thm_PiecesCounted_steps_le_of_le
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {D : Data} {ρ : ℝ} {c c' k : ℕ} (hD : D.Is ρ c) (hk : k ≤ c) (hc : c ≤ c') (hk' : k + 1 ≤ c') {f : (List Unit × Question) × List Unit → Answer}
    (hf : ∀ g a, D.oracle g = some a → f (g, List.replicate (2 ^ (k * g.1.length)) ()) = a) : Computes (padThen (fun g => 2 ^ (k * g.1.length)) f) D c' := by
  intro g a hg
  have hl := (oracle_eq_some hg).1
  have h1 := hD.size_question_le' hg
  have h2 := hD.size_answer_le' hg
  have h3 : 2 ^ (k * g.1.length) ≤ 2 ^ (c * g.1.length) := steps_le_of_le _ hk
  have h4 := room_eq c g.1.length
  have h5 := room_le_of_le hl hc
  have h6 : size (2 ^ (k * g.1.length)) ≤ 2 ^ (k * g.1.length) + 1 := by
    have := Nat.size_le.2 (Nat.lt_two_pow_self (n := 2 ^ (k * g.1.length)))
    rw [size_nat]
    omega
  have r := padThen_runs (fun g : List Unit × Question => 2 ^ (k * g.1.length)) f g (S := room c' g.1.length) (by omega) (by rw [hf g a hg]; omega)
  rw [hf g a hg] at r
  refine r.mono ?_ le_rfl
  have h7 : 2 ^ ((k + 1) * g.1.length) = 2 ^ (k * g.1.length) * 2 ^ g.1.length := by rw [Nat.add_mul, Nat.one_mul, pow_add]
  have h8 : 2 ≤ 2 ^ g.1.length := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g.1.length := Nat.pow_le_pow_right (by norm_num) hl
  have h9 := Nat.mul_le_mul_left (2 ^ (k * g.1.length)) h8
  have h10 : 1 ≤ 2 ^ (k * g.1.length) := Nat.one_le_two_pow
  have h11 : 2 ^ ((k + 1) * g.1.length) ≤ 2 ^ (c' * g.1.length) := steps_le_of_le _ hk'
  change 2 ^ (k * g.1.length) + 1 ≤ 2 ^ (c' * g.1.length)
  omega
end PiecesCounted
