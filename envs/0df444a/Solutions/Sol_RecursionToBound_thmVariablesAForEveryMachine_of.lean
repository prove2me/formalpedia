-- Prove2me | solution 1 for RecursionToBound.thmVariablesAForEveryMachine_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:42:47.447654+00:00
-- url     : https://prove2.me/submissions/67786eff-e248-48cf-a639-6b6f1d685b61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_End
import Theorems.Thm_RecursionToBound_steps_le_timeVariablesA
import Theorems.Thm_ClauseBound_Alg_End_fmlOf_enc
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_CertNet_nU
import Theorems.Thm_PairsToBound_expVariablesA_mono
import Theorems.Thm_PairsToBound_widthOr3Stmt
import Theorems.Thm_RecursionToBound_cutOffIsIdle
import Theorems.Thm_RecursionToBound_exponentIsWithinTheBound
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_UniformInK_Time_length_enc_succ_le
import Theorems.Thm_VariableBound_Net_Main_u
import Theorems.Thm_VariableBound_Paper_one_le_lg
import Theorems.Thm_VariableBound_VariablesA_K_strictMono
import Theorems.Thm_VariableBound_VariablesA_e_ge_n
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_lg_div_facts
import Theorems.Thm_VariableBound_VariablesA_stepSparsifyLarge
import Theorems.Thm_VariableBound_VariablesA_stepSparsifySmall
import Theorems.Thm_Wrap_Outputs_mono
attribute [local fun_prop] PaddedDescent.F.CertNet.nU



set_option autoImplicit false
section
section
open RecursionToBound
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End UniformInK Wrap MainTheoremForms PairsToBound VariableBound.Paper
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution (hRight : CountIsRight) (hPoly : CountIsPolynomialTime) (hPlan : PlanFailsOnlyAboveN) (hWidth : WidthOnTheCode) : ThmVariablesAForEveryMachine := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀a, hR⟩ := hRight Idx S e C₀ Q hS num hnum
  obtain ⟨A, n₁a, hA⟩ := exponentIsWithinTheBound Idx S e C₀ Q hS num hnum
  obtain ⟨n₁b, hL⟩ := VariableBound.VariablesA.stepSparsifyLarge C₀
  refine ⟨max n₀a (max n₁a n₁b), fun n₁ hn₁ => ⟨?_, fun M q hM => ?_⟩⟩
  · obtain ⟨hp1, hp2⟩ := hPoly Idx S hS n₁ Q.pick num Q.pick_poly hnum.1
    obtain ⟨M, q, hf, hM⟩ := CountKSatRate.stPaddedW _ _ hp2 hp1
    exact ⟨M, q, hf, hM⟩
  obtain ⟨c, hc⟩ := VariableBound.VariablesA.stepSparsifySmall C₀ n₁
  refine ⟨q * 12 * (c + A + 1), fun k n l φ hl hk hk4 hφ => ?_⟩
  have hn₀a : n₀a ≤ n₁ := (le_max_left _ _).trans hn₁
  have hn₁a : n₁a ≤ n₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn₁
  have hn₁b : n₁b ≤ n₁ := ((le_max_right _ _).trans (le_max_right _ _)).trans hn₁
  have hk1 : 1 ≤ k := by omega
  have h0 : S.K (Q.idx 0) ^ 17 ≤ n := (Nat.pow_le_pow_left ((VariableBound.VariablesA.K_strictMono Q).monotone (Nat.zero_le l)) 17).trans hl.1
  have hn4 : 4 ≤ n := by
    have := (Nat.pow_le_pow_left (Q.K_two l) 17).trans hl.1
    omega
  have he0 := VariableBound.VariablesA.e_pos Q l
  have he1 := Q.e_le l
  have hen := VariableBound.VariablesA.e_ge_n Q hl
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hLg := one_le_lg (m := n) (by omega)
  -- what the function reads from the code
  have hnU : nU (SatM.enc k φ) = n := by
    unfold nU
    rw [fmlOf_enc hk1 hφ.1, List.length_replicate]
  have hw := hWidth.1 k n φ hk1 hφ
  obtain ⟨hnum', hidx⟩ := hWidth.2 Idx S e C₀ Q num k n l φ hk1 hφ hl
  obtain ⟨hw3, -, hwle⟩ := widthOr3Stmt n φ
  have hwk : widthOr3 φ ≤ k := by
    have := (hwle k hk1 hφ).1
    omega
  have hw4 : ((widthOr3 φ : ℕ) : ℝ) ^ 4 ≤ lg n := (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hwk) 4).trans hk4
  have hcut := cutOffIsIdle (widthOr3 φ) n (by omega) hw4
  have hexpo : expo S n₁ Q.pick num (SatM.enc k φ) =
      (planAt S n₁ (widthOr3 φ) n (Q.idx l) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()))).getD n := by
    unfold expo plan
    rw [hw, hnU, hcut, hidx, hnum']
  -- X ≥ 0
  obtain ⟨w1, w2⟩ := VariableBound.VariablesA.lg_div_facts hk he0 he1
  have hX0 : 0 ≤ expVariablesA k n (e l) := by
    unfold expVariablesA
    have : 0 ≤ lg (k / e l) := by linarith
    positivity
  have up : ∀ b : ℕ, b ≤ c + A + 1 → (b : ℝ) * expVariablesA k n (e l) ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) := fun b hb =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hX0
  -- the three bounds
  have key : 1 ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) ∧ ((expo S n₁ Q.pick num (SatM.enc k φ) : ℕ) : ℝ) ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) ∧
      (k : ℝ) * lg n ≤ ((c + A + 1 : ℕ) : ℝ) * expVariablesA k n (e l) := by
    by_cases hsmall : n < n₁
    · obtain ⟨s1, s2⟩ := hc k n (e l) (by omega) hsmall hk hen he1
      have hE : expo S n₁ Q.pick num (SatM.enc k φ) = n := by
        rw [hexpo]
        unfold planAt
        rw [if_neg (not_le.2 hsmall)]
        rfl
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have u := up c (by omega)
      rw [hE]
      exact ⟨by linarith, by linarith, by linarith⟩
    · have hge : n₁ ≤ n := not_lt.1 hsmall
      have s1 := hL k n (e l) (hn₁b.trans hge) hk4 hen
      have s2 : e l * n ≤ expVariablesA k n (e l) := by
        have g1 : 1 ≤ (k : ℝ) ^ 2 * lg (k / e l) := by nlinarith
        have g2 : 0 ≤ e l * n := by positivity
        calc e l * n = 1 * (e l * n) := (one_mul _).symm
          _ ≤ (k : ℝ) ^ 2 * lg (k / e l) * (e l * n) := mul_le_mul_of_nonneg_right g1 g2
          _ = expVariablesA k n (e l) := by unfold expVariablesA; ring
      have s3 : (1 : ℝ) ≤ k * lg n := by nlinarith
      have hAx := hA (widthOr3 φ) n l (hn₁a.trans hge) hl hw3 hw4
      have hmono := expVariablesA_mono (n := n) hw3 hwk he0 he1
      have hAx' : ((needOutputs S (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) (Q.idx l) n +
          needWalk (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) n : ℕ) : ℝ) ≤ (A : ℝ) * expVariablesA k n (e l) :=
        hAx.trans (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg A))
      obtain ⟨p1, p2⟩ := hPlan Idx S hS n₁ (widthOr3 φ) n (Q.idx l) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()))
      have hE : expo S n₁ Q.pick num (SatM.enc k φ) ≤ needOutputs S (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) (Q.idx l) n +
          needWalk (widthOr3 φ) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) n := by
        rw [hexpo]
        cases hp : planAt S n₁ (widthOr3 φ) n (Q.idx l) (num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())) with
        | none => exact (p2 hp hge).le
        | some v => exact (p1 v hp).2.1.le
      have hE' : ((expo S n₁ Q.pick num (SatM.enc k φ) : ℕ) : ℝ) ≤ (A : ℝ) * expVariablesA k n (e l) := le_trans (by exact_mod_cast hE) hAx'
      have u1 := up 1 (by omega)
      have u2 := up A (by omega)
      rw [Nat.cast_one, one_mul] at u1
      exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨k1, k2, k3⟩ := key
  have hcount := hR n₁ hn₀a k n φ h0 hk hk4 hφ (PaddedDescent.pad (expo S n₁ Q.pick num (SatM.enc k φ))) (by rw [PaddedDescent.pad, List.length_replicate])
  have hrun := hM (SatM.enc k φ)
  rw [hcount] at hrun
  exact Outputs.mono hrun (steps_le_timeVariablesA q (c + A + 1) k1 k2 k3 hn4 (UniformInK.Time.length_enc_succ_le hk1 hφ))
end RecursionToBound
