-- Prove2me | solution 1 for Printed.eStar_le_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:16:23.82802+00:00
-- url     : https://prove2.me/submissions/19cd4f3b-e68e-4498-be35-3e21dce59561

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelCost
import Definitions.Def_Eight_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Printed_LevelSentences
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_achievable_of_eStar_lt
import Theorems.Thm_Paper_eStar_le
import Theorems.Thm_Paper_eStar_nonneg
import Theorems.Thm_Printed_achievable_of_eStar_lt
import Theorems.Thm_Printed_eStar_le
import Theorems.Thm_Printed_eStar_nonneg
import Theorems.Thm_Printed_stMono
import Theorems.Thm_QueryMachines_stMono


set_option autoImplicit false
section
section
open Printed
open Eight Paper QueryMachines
namespace Printed
theorem _root_.solution (hP3 : LevelProposition) {e e'' : ℝ} (he : eStar < e) (he'' : rho * e < e'') : eStar ≤ e'' := by
  have hs0 := eStar_nonneg
  have h0 : 0 ≤ e := by linarith
  have hd : 0 < e'' - rho * e := by linarith
  refine eStar_le fun K₀ => ?_
  obtain ⟨K, hK, hA⟩ := achievable_of_eStar_lt he (max K₀ (max 2 ⌈(2 * e + 2) / (e'' - rho * e)⌉₊))
  have hK0 : K₀ ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans hK
  have hKd : (2 * e + 2) / (e'' - rho * e) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans hK)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hsmall : (2 * e + 2) / (K : ℝ) ≤ e'' - rho * e := by
    rw [div_le_iff₀ hd] at hKd
    rw [div_le_iff₀ hKpos]
    linarith
  have hexp : (rho + 2 / K) * e + 2 / K ≤ e'' := by
    have : (rho + 2 / K) * e + 2 / K = rho * e + (2 * e + 2) / (K : ℝ) := by ring
    linarith
  refine ⟨(3 * K ^ 8) ^ 2, ?_, stMono _ _ _ (hP3 K e hA) hexp⟩
  have h1 : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
  have h2 : 3 * K ^ 8 ≤ (3 * K ^ 8) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega
end Printed
