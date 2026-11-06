-- Prove2me | solution 1 for SparsificationLemma.Cal.sparsABC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:48:31.489377+00:00
-- url     : https://prove2.me/submissions/1b53f22a-63bb-4976-9cae-777912ed67df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_SparsificationLemma_One
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsificationLemma_Cal_Main
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Cal_factIIIy
import Theorems.Thm_SparsificationLemma_Cal_gen
import Theorems.Thm_SparsificationLemma_Cal_stDegSum
import Theorems.Thm_SparsificationLemma_stExactlyOne
import Theorems.Thm_SparsificationLemma_stNoTaut


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat
namespace SparsificationLemma.Cal
theorem _root_.solution (hN : StNodup) (hA : StAlpha) (hY : StYLe) (hDeg : StDegLe) : SparsABC := by
  intro k n ε φ hk h0 h1 hφ
  obtain ⟨a1, a2, -, a4, -⟩ := hA k ε hk h0 h1
  obtain ⟨t1, t2, -⟩ := stNoTaut φ
  have hα : 1 ≤ alphaC k ε := by omega
  have hψ := t2 k n hφ
  obtain ⟨-, -, g3, -⟩ := gen hα (by omega : 1 ≤ k) hψ
  have hε : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have hx : ((xC k ε : ℚ) : ℝ) = 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by rw [xC]; push_cast; ring
  refine ⟨fun Φ hΦ => ⟨(g3 Φ hΦ).1, hN _ _ _ _ Φ hΦ⟩, ?_, fun b => ?_, fun Φ hΦ v => ?_⟩
  · have hy : yC k (alphaC k ε) ≤ (ε : ℝ) := by
      refine hY k (alphaC k ε) (ε : ℝ) (by omega) hε ?_ ?_
      · rw [← hx]; exact_mod_cast a1
      · rw [← hx]; exact a4
    have h3 := factIIIy (alphaC k ε) k n (noTaut φ) hα (by omega) hψ
    rw [sparsify, outputs, List.length_map]
    exact h3.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg n)))
  · obtain ⟨e1, e2⟩ := stExactlyOne (thetaC (alphaC k ε)) k (depthC (alphaC k ε) k n) (noTaut φ) b
    exact ⟨fun h => e1 ((t1 b).2 h), fun h => e2 fun h' => h ((t1 b).1 h')⟩
  · have c1 := (g3 Φ hΦ).2 v
    have c2 := (stDegSum (alphaC k ε) k hα (by omega)).2.1
    have c3 := hDeg k ε hk h0 h1
    have c4 : occN Φ v ≤ 2 * (2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2)) + 2 := by omega
    have c5 : (occN Φ v : ℝ) ≤ 2 * ((2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) : ℕ) : ℝ) + 2 := by exact_mod_cast c4
    linarith
end SparsificationLemma.Cal
