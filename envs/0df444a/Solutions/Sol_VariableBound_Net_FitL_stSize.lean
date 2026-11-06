-- Prove2me | solution 1 for VariableBound.Net.FitL.stSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:44:33.757093+00:00
-- url     : https://prove2.me/submissions/b51842ee-5aed-4793-8eec-e5dcaae78ebc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Net_Fit
import Theorems.Thm_VariableBound_Net_FitL_lg_two_mul_le
import Theorems.Thm_VariableBound_Net_FitL_nb_pos
import Theorems.Thm_VariableBound_Net_FitL_nb_le
import Theorems.Thm_VariableBound_Net_FitL_sized_mono
import Theorems.Thm_VariableBound_Net_FitL_ub_real
import Theorems.Thm_VariableBound_Net_FitL_small_le_PbD
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_r_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_sized_mono
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.FitL
open Groundwork PaddedDescent.F
open PaddedDescent.F.Mark (qv WfL occ nProf)
open ClauseBound.ParityChecks (LD)
namespace VariableBound.Net.FitL
theorem _root_.solution (hp : VariableBound.ParamIneq) (hU : StUPrinted) (hS : StSized) (hs : StSmall) : StSize := by
  intro k K n Δ nb M D fl y hK hF hy
  have hg : 0 < 3 * K ^ 8 := by positivity
  rcases Nat.lt_or_ge nb D.1.length with hlt | hle
  · obtain ⟨hr, h1, hrow⟩ := hF.big hlt
    constructor
    · have hsb : ∀ L ∈ D.2, (L.length : ℚ) ≤ (sbMax Δ : ℚ) := by
        intro L hL
        have hnb : (0 : ℝ) < nb := by exact_mod_cast nb_pos hF.isNb
        have a : (L.length : ℝ) ≤ 16 * (D.1.length : ℝ) / nb := by
          rw [le_div_iff₀ hnb, mul_comm]
          exact_mod_cast hrow L hL
        have b := (hp.sb_lt n Δ D.1.length nb hF.two hF.m_le hF.isNb).2
        have c : 32 * (Δ : ℝ) * lg (2 * Δ) ≤ 32 * Δ * LD Δ := by
          have := lg_two_mul_le Δ
          gcongr
        have d : (L.length : ℝ) ≤ ((sbMax Δ : ℕ) : ℝ) := by
          unfold sbMax
          push_cast
          linarith
        exact_mod_cast d
      refine sized_mono (hS k (3 * K ^ 8) n Δ nb M (tbMax n Δ) (10 * n) (sbMax Δ : ℚ) D fl y hg (Nat.cast_nonneg _) hF.wf hF.occ_le hF.r_le hsb hF.col hy) le_rfl ?_
      unfold BbD BD
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hF.M_le) _
    · have h2 := (hU k (3 * K ^ 8) n Δ nb M D fl y hg ⟨hF.wf, hF.two, hF.occ_le, hF.m_le, hF.isNb, hlt, hr, h1, hrow⟩ hF.M_le hy).trans (ub_real k K n hF.two)
      exact_mod_cast h2
  · obtain ⟨ψ, Lam⟩ := D
    obtain rfl : Lam = [] := hF.small hle
    obtain ⟨h1, h2⟩ := hs k (3 * K ^ 8) n Δ nb M ψ fl y hg hF.wf hF.occ_le hle hy
    refine ⟨sized_mono h1 (small_le_PbD K n Δ) (by unfold BbD BD; omega), h2.trans ?_⟩
    have hnb : nb ≤ n := nb_le hF.isNb (by have := hF.two; omega)
    unfold UbD
    have e : 6 * k * (n + LD Δ) = 6 * (k * n) + 6 * (k * LD Δ) := by ring
    have h3 : 2 * (k - 1) * nb ≤ 2 * k * n := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le k 1)) hnb
    have e2 : 2 * k * n = 2 * (k * n) := by ring
    omega
end VariableBound.Net.FitL
