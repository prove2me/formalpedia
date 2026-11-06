-- Prove2me | solution 1 for SparsificationLemma.Mach.sparsABCD_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:11.006638+00:00
-- url     : https://prove2.me/submissions/2d4a6ac1-a3b5-4964-ac77-67b0cfc31027

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Geo_S
import Definitions.Def_SparsificationLemma_Mach_Len
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_Full
import Theorems.Thm_SparsificationLemma_Mach_div_le_two_pow_precE
import Theorems.Thm_SparsificationLemma_Mach_two_pow_betaU_le
import Theorems.Thm_SparsificationLemma_Mach_mul_div_le_eps
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Mach_isKCNF_toN
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (hS : StThmS) (hP : Prints) : SparsABCD := by
  obtain ⟨M, C₀, hfin, hM⟩ := hP
  refine ⟨M, C₀ + 81, hfin, fun k n ε φ hk h0 h1 hφ hne => ?_⟩
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have hs0 : s0U k ≤ precE (C₀ + 81) k ε := le_max_left _ _
  have hsC := div_le_two_pow_precE (C₀ + 81) k ε
  have hc := two_pow_betaU_le (C := C₀ + 81) (by omega) hk h0 h1
  generalize hs : precE (C₀ + 81) k ε = s at *
  obtain ⟨-, g2, g3, -, g5, g6⟩ := hS k n s (Decode.toN φ) hk hs0 (isKCNF_toN hφ.1 hne)
  refine ⟨outTau k n (tauOf s) (Decode.toN φ), _, hM k n s φ hk hs0 hφ hne, g2, ?_, g5, fun Ψ hΨ v => ?_, ?_⟩
  · refine g3.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    have h2 : ((C₀ + 81 : ℕ) : ℝ) ≤ (ε : ℝ) * (2 : ℝ) ^ s := by rwa [div_le_iff₀ h0R, mul_comm] at hsC
    have h3 : (1 : ℝ) ≤ ((C₀ + 81 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ C₀ + 81)
    rw [div_le_iff₀ hp]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · calc (occN Ψ v : ℝ) ≤ ((2 ^ betaU k s : ℕ) : ℝ) := by exact_mod_cast g6 Ψ hΨ v
      _ = (2 : ℝ) ^ betaU k s := by push_cast; rfl
      _ ≤ _ := hc
  · have hL : (1 : ℝ) ≤ ((encIn s k φ).length : ℝ) + 2 ^ k := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      linarith [Nat.cast_nonneg (α := ℝ) (encIn s k φ).length]
    have e1 : ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) := by
      have := mul_div_le_eps (c := C₀) (C := C₀ + 81) (n := n) (s := s) (by omega) h0R hsC
      calc ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) = (2 : ℝ) ^ (((C₀ * (n / 2 ^ s) : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
    have e2 : (((encIn s k φ).length : ℝ) + 2 ^ k) ^ C₀ ≤ (((encIn s k φ).length : ℝ) + 2 ^ k) ^ (C₀ + 81) :=
      pow_le_pow_right₀ hL (by omega)
    have e3 : (C₀ : ℝ) ≤ ((C₀ + 81 : ℕ) : ℝ) := by exact_mod_cast (by omega : C₀ ≤ C₀ + 81)
    calc ((C₀ * ((encIn s k φ).length + 2 ^ k) ^ C₀ * 2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ)
        = (C₀ : ℝ) * (((encIn s k φ).length : ℝ) + 2 ^ k) ^ C₀ * ((2 ^ (C₀ * (n / 2 ^ s)) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((C₀ + 81 : ℕ) : ℝ) * (((encIn s k φ).length : ℝ) + 2 ^ k) ^ (C₀ + 81) * (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) :=
        mul_le_mul (mul_le_mul e3 e2 (by positivity) (by positivity)) e1 (by positivity) (by positivity)
end SparsificationLemma.Mach
