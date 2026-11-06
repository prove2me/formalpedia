-- Prove2me | solution 1 for SparsificationLemma.Mach.lemSparsification_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:53:21.195202+00:00
-- url     : https://prove2.me/submissions/8b179d30-f72e-4768-9433-7c6655f97c8a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Theorems.Thm_SparsificationLemma_Mach_poly_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le
import Theorems.Thm_Groundwork_Decode_satN_toN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_stLenOfOcc
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (h : SparsABCD) : LemSparsification := by
  obtain ⟨M, C, hfin, hM⟩ := h
  refine ⟨M, hfin, fun ε hε => ?_⟩
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hε one_pos)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hqε : (q : ℝ) ≤ ε := (hq1.trans_le (min_le_left _ _)).le
  have hq1' : q ≤ 1 := by exact_mod_cast (hq1.trans_le (min_le_right _ _)).le
  refine ⟨⌈((C : ℝ) * ((3 : ℕ) : ℝ) / (q : ℝ)) ^ (16 * 3)⌉₊ + 1, precE C 3 q, C * (precE C 3 q + 412) ^ C + 4 * C, by omega,
    fun n φ h3 hne => ?_⟩
  have h3' : SatK.IsKCNF 3 φ := ⟨h3.1, h3.2⟩
  obtain ⟨Φ, T, hrun, g1, g2, g3, g4, g5⟩ := hM 3 n q φ (by norm_num) hq0' hq1' h3' hne
  have hmono : (2 : ℝ) ^ ((q : ℝ) * (n : ℝ)) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hqε (Nat.cast_nonneg _))
  refine ⟨Φ, T, hrun, ?_, g2.trans hmono, fun Ψ hΨ => ⟨(g1 Ψ hΨ).1, (g1 Ψ hΨ).2, ?_⟩, ?_⟩
  · have hN := poly_le C (precE C 3 q) h3'
    have hR : (C : ℝ) * (((encIn (precE C 3 q) 3 φ).length : ℝ) + 2 ^ 3) ^ C
        ≤ ((C * (precE C 3 q + 412) ^ C + 4 * C : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C * (precE C 3 q + 412) ^ C + 4 * C) := by
      exact_mod_cast hN
    calc (T : ℝ) ≤ (C : ℝ) * (((encIn (precE C 3 q) 3 φ).length : ℝ) + 2 ^ 3) ^ C * (2 : ℝ) ^ ((q : ℝ) * (n : ℝ)) := g5
      _ ≤ ((C * (precE C 3 q + 412) ^ C + 4 * C : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (C * (precE C 3 q + 412) ^ C + 4 * C)
            * (2 : ℝ) ^ (ε * (n : ℝ)) := mul_le_mul hR hmono (by positivity) (by positivity)
      _ = _ := by ring
  · refine stLenOfOcc 3 n _ Ψ (g1 Ψ hΨ).1 fun v => ?_
    have h1 : (occN Ψ v : ℝ) ≤ (⌈((C : ℝ) * ((3 : ℕ) : ℝ) / (q : ℝ)) ^ (16 * 3)⌉₊ : ℝ) := (g4 Ψ hΨ v).trans (Nat.le_ceil _)
    have h2 : occN Ψ v ≤ ⌈((C : ℝ) * ((3 : ℕ) : ℝ) / (q : ℝ)) ^ (16 * 3)⌉₊ := by exact_mod_cast h1
    omega
  · rw [← Decode.satN_toN]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hi, -⟩ := (g3 b).1 hb
      exact ⟨Φ.get i, List.get_mem _ _, b, hi⟩
    · rintro ⟨Ψ, hΨ, b, hb⟩
      by_contra hno
      exact (g3 b).2 (fun hs => hno ⟨b, hs⟩) Ψ hΨ hb
end SparsificationLemma.Mach
