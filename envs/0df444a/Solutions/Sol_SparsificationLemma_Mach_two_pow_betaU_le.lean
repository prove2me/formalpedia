-- Prove2me | solution 1 for SparsificationLemma.Mach.two_pow_betaU_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:52:03.933193+00:00
-- url     : https://prove2.me/submissions/3482cb19-c45d-49ee-969d-b004dd3f687b

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
import Theorems.Thm_SparsificationLemma_Mach_two_pow_precE_le
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution {C k : ℕ} {ε : ℚ} (hC : 81 ≤ C) (hk : 1 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (2 : ℝ) ^ betaU k (precE C k ε) ≤ ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ (16 * k) := by
  have hCR : (81 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hs := two_pow_precE_le (by omega : 1 ≤ C) hk h0 h1
  generalize (C : ℝ) * (k : ℝ) / (ε : ℝ) = B at *
  generalize precE C k ε = s at *
  have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hs' : (2 : ℝ) ^ s ≤ 4 / 81 * B ^ 2 := by nlinarith
  have hB8 : 0 ≤ B ^ 8 := by positivity
  have e1 : (2 : ℝ) ^ (4 * s + 17) ≤ B ^ 8 := by
    calc (2 : ℝ) ^ (4 * s + 17) = ((2 : ℝ) ^ s) ^ 4 * 2 ^ 17 := by rw [pow_add, pow_mul']
      _ ≤ (4 / 81 * B ^ 2) ^ 4 * 2 ^ 17 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.le hs' 4) (by positivity)
      _ = 33554432 / 43046721 * B ^ 8 := by ring
      _ ≤ B ^ 8 := by linarith
  calc (2 : ℝ) ^ betaU k s = ((2 : ℝ) ^ (4 * s + 17)) ^ (2 * k) := by rw [betaU, ← pow_mul]; congr 1; ring
    _ ≤ (B ^ 8) ^ (2 * k) := pow_le_pow_left₀ (by positivity) e1 _
    _ = B ^ (16 * k) := by rw [← pow_mul]; congr 1; ring
end SparsificationLemma.Mach
