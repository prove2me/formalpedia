-- Prove2me | solution 1 for SparsificationLemma.Mach.two_pow_precE_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:44:14.793947+00:00
-- url     : https://prove2.me/submissions/cea3d137-d31e-4c70-94b6-b6aef92fcbbd

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
import Theorems.Thm_SparsificationLemma_Mach_two_pow_s0U_le
import Theorems.Thm_SparsificationLemma_Mach_two_pow_clog_le

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution {C k : ℕ} {ε : ℚ} (hC : 1 ≤ C) (hk : 1 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (C : ℝ) * (2 : ℝ) ^ precE C k ε ≤ 4 * ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ 2 := by
  have hCR : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hA : (C : ℝ) ≤ (C : ℝ) / (ε : ℝ) := by rw [le_div_iff₀ h0R]; nlinarith
  have hB : (C : ℝ) * (k : ℝ) / (ε : ℝ) = (C : ℝ) / (ε : ℝ) * (k : ℝ) := by ring
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
  rw [hB, mul_pow]
  rcases le_total (s0U k) (Nat.clog 2 ⌈(C : ℚ) / ε⌉₊) with h | h
  · rw [precE, max_eq_right h]
    have hq : 0 < (C : ℚ) / ε := by positivity
    have hN : 1 ≤ ⌈(C : ℚ) / ε⌉₊ := Nat.ceil_pos.2 hq
    have a1 := two_pow_clog_le hN
    have a2 : (⌈(C : ℚ) / ε⌉₊ : ℚ) < (C : ℚ) / ε + 1 := Nat.ceil_lt_add_one hq.le
    have a3 : (⌈(C : ℚ) / ε⌉₊ : ℝ) < (C : ℝ) / (ε : ℝ) + 1 := by exact_mod_cast a2
    have a4 : (2 : ℝ) ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ 2 * (⌈(C : ℚ) / ε⌉₊ : ℝ) := by exact_mod_cast a1
    generalize (C : ℝ) / (ε : ℝ) = A at *
    have a5 : (2 : ℝ) ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ 4 * A := by linarith
    calc (C : ℝ) * (2 : ℝ) ^ Nat.clog 2 ⌈(C : ℚ) / ε⌉₊ ≤ A * (4 * A) := mul_le_mul hA a5 (by positivity) (by linarith)
      _ = 4 * (A ^ 2 * 1) := by ring
      _ ≤ 4 * (A ^ 2 * (k : ℝ) ^ 2) := by gcongr
  · rw [precE, max_eq_left h]
    have a1 : (2 : ℝ) ^ s0U k ≤ 4 * (k : ℝ) ^ 2 := by exact_mod_cast two_pow_s0U_le hk
    generalize (C : ℝ) / (ε : ℝ) = A at *
    have a2 : (C : ℝ) ≤ A ^ 2 := by nlinarith
    calc (C : ℝ) * (2 : ℝ) ^ s0U k ≤ A ^ 2 * (4 * (k : ℝ) ^ 2) := mul_le_mul a2 a1 (by positivity) (by positivity)
      _ = 4 * (A ^ 2 * (k : ℝ) ^ 2) := by ring
end SparsificationLemma.Mach
