-- Prove2me | solution 1 for PrintedOrder.tiedFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:49:15.368233+00:00
-- url     : https://prove2.me/submissions/c33dcd9e-89db-49c6-a2d9-1d47321ae338

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_PrintedOrder_AddUp
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Counting
import Theorems.Thm_PrintedOrder_countsFrom
import Theorems.Thm_CountKSat_EndLemmas_CountsTM_mono
import Theorems.Thm_CountKSat_stHostW
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SplitCount_counts_of_simulation
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal
namespace PrintedOrder
theorem _root_.solution : SplitCount.StStepTwo → SplitCount.StTiedTM := by
  intro h2 k hk δ hδ
  obtain ⟨ℓ, τ, ⟨hI⟩, c₁, h⟩ := countsFrom h2 k hk (δ / 2) (by positivity)
  have := hI
  obtain ⟨N', q, hfin, hP⟩ := stHostW (COUNTsplit k ℓ τ)
  have hP' : ∀ (x w : List Bool) (T S : ℕ), (COUNTsplit k ℓ τ).Runs x T S w →
      Nonempty (Turing.TM2OutputsInTime N'.tm (x.map N'.inputAlphabet.invFun) (some (w.map N'.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q)) :=
    fun x w T S r => hP x T S w r
  obtain ⟨C, hC⟩ := counts_of_simulation hδ (COUNTsplit k ℓ τ) N' q hP' c₁ _ _ (fun n φ h => DecodeK.length_enc_succ_le h) h
  refine ⟨ℓ, τ, N', max c₁ C, q, hfin, ⟨hI⟩, fun n φ h3 => ?_, hP', ?_⟩
  · obtain ⟨T, r, hT⟩ := h n φ h3
    refine ⟨T, r.mono le_rfl (Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right (by omega) (le_max_left _ _))), hT.trans ?_⟩
    have hn0 : (0 : ℝ) ≤ δ * n := by positivity
    exact mul_le_mul (by exact_mod_cast le_max_left c₁ C) (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)) (by positivity) (by positivity)
  · exact EndLemmas.CountsTM.mono hC fun n => Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right c₁ C) (by positivity))
end PrintedOrder
