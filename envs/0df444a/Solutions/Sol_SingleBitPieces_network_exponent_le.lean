-- Prove2me | solution 1 for SingleBitPieces.network_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:32:16.076115+00:00
-- url     : https://prove2.me/submissions/89b59c87-6703-443f-9245-7ba14c3defba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork Groundwork.Prog Finset Paper
namespace SingleBitPieces
theorem _root_.solution {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U ≤ 6 * m)
    (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K ≤ 97 / 144 * δ' * m + 25 / 144 * δ' * g := by
  have hK72 : (72 : ℝ) ≤ K := by
    have : (72 : ℝ) ≤ 72 / δ' := by rw [le_div_iff₀ hδ']; nlinarith
    linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hKδ : 72 ≤ δ' * K := by
    rw [div_le_iff₀ hδ'] at hK
    linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (g : ℝ) * P / K := ⟨_, rfl⟩
  have hqK : q * K = (g : ℝ) * P := by rw [hq]; field_simp
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hU' : (U : ℝ) ≤ 6 * m := by exact_mod_cast hU
  have hP' : (g : ℝ) * P ≤ 6 * ((m : ℝ) + g) := by exact_mod_cast hP
  have hmg : (0 : ℝ) ≤ (m : ℝ) + g := by positivity
  -- q ≤ (m + g)/12 and q ≤ δ'(m + g)/12
  have a1 : 72 * q ≤ 6 * ((m : ℝ) + g) := by nlinarith
  have a2 : 72 * q ≤ δ' * (6 * ((m : ℝ) + g)) := by
    calc 72 * q ≤ δ' * K * q := mul_le_mul_of_nonneg_right hKδ hq0
      _ = δ' * (q * K) := by ring
      _ ≤ δ' * (6 * ((m : ℝ) + g)) := by rw [hqK]; exact mul_le_mul_of_nonneg_left hP' hδ'.le
  have e1 : 2 * (g : ℝ) * P / K = 2 * q := by rw [hq]; ring
  rw [e1, ← hq]
  nlinarith
end SingleBitPieces
