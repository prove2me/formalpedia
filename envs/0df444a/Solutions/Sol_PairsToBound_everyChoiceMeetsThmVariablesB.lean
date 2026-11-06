-- Prove2me | solution 1 for PairsToBound.everyChoiceMeetsThmVariablesB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:30.745358+00:00
-- url     : https://prove2.me/submissions/6b56f2a3-50bf-4594-877f-8969155edc43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_FrontEnd
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_TwoMachines_Main
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_PairsToBound_Main
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_ClauseBound_TopN_Arith_le_of_small
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_PairsToBound_fall_back_case_le
import Theorems.Thm_PairsToBound_le_of_small
import Theorems.Thm_PairsToBound_le_of_wide
import Theorems.Thm_PairsToBound_length_enc_succ_le
import Theorems.Thm_PairsToBound_mainRegimeBound
import Theorems.Thm_PairsToBound_main_case_le
import Theorems.Thm_PairsToBound_widthOr3Stmt
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_UniformInK_Time_length_enc_succ_le
import Theorems.Thm_VariableBound_Paper_two_le_expN
import Theorems.Thm_Wrap_Outputs_mono


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : EveryChoiceMeetsThmVariablesB := by
  intro Idx _ S e C₀ Q a he M C' hM Mb c hMb pre test hpre htest N q hN
  obtain ⟨C₁, hC₁⟩ := mainRegimeBound Idx S e C₀ Q a he M C' hM
  obtain ⟨D, hD⟩ := exists_nat_ge (Real.sqrt (17 * lg (S.K (Q.idx 0))))
  refine ⟨q * (9 * C₁ + c * (D + 9 + 1) + 10 + 2), fun k n φ hk hn hφ => ?_⟩
  obtain ⟨hw3, hwk, hwle⟩ := widthOr3Stmt n φ
  obtain ⟨-, hw9⟩ := hwle k hk hφ
  have hlen := UniformInK.Time.length_enc_succ_le hk hφ
  by_cases ht : test (SatM.enc k φ) = true
  · obtain ⟨t1, t2⟩ := (htest k n φ hk hφ).1 ht
    have hrun : Outputs M (pre (SatM.enc k φ)) (SatK.binary n (SatK.numSat φ)) (timeN C₁ (widthOr3 φ) n) := by
      rw [hpre k n φ hk hφ]
      exact hC₁ _ n φ t1 hw3 t2 (hwk hφ.2)
    exact Outputs.mono ((hN _ _ _).1 ht hrun) (main_case_le q C₁ _ (by omega) (by omega) hk hn hw9 hlen)
  · have hf : test (SatM.enc k φ) = false := Bool.eq_false_iff.2 ht
    have hrun : Outputs Mb (id (SatM.enc k φ)) (SatK.binary n (SatK.numSat φ)) (2 ^ (c * n) * n ^ (c * k)) := hMb k n φ hk (by omega) hφ
    have hnD : (n : ℝ) ≤ ((D + 9 : ℕ) : ℝ) * expN k n := by
      have hX := two_le_expN hk hn
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
      by_cases hs : S.K (Q.idx 0) ^ 17 ≤ n
      · have hwide : lg n < ((widthOr3 φ : ℕ) : ℝ) ^ 4 := by
          by_contra hh
          exact ht ((htest k n φ hk hφ).2 ⟨hs, not_lt.1 hh⟩)
        have := le_of_wide hn hwide hw9
        push_cast
        nlinarith
      · have := le_of_small (Q.K_two 0) hk hn (not_le.1 hs) hD
        push_cast
        nlinarith
    exact Outputs.mono ((hN _ _ _).2 hf hrun) (fall_back_case_le q c (D + 9) _ (by omega) (by omega) hk hn hnD hlen)
end PairsToBound
