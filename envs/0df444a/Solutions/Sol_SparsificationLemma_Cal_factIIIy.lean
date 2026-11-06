-- Prove2me | solution 1 for SparsificationLemma.Cal.factIIIy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:04.480886+00:00
-- url     : https://prove2.me/submissions/d1b93a3b-7cfa-4ed9-afd0-25d8aa43ec84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Facts
import Theorems.Thm_SparsificationLemma_Cal_gen
import Theorems.Thm_SparsificationLemma_Cal_log_le_yC
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Cal_factIV
import Theorems.Thm_SparsificationLemma_Cal_sum_range_betaC
import Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
namespace SparsificationLemma.Cal
theorem _root_.solution : FactIIIy := by
  intro α k n ψ hα hk hψ
  have h1 := (gen hα (by omega : 1 ≤ k) hψ).2.1
  rw [outputs, List.length_map] at h1
  have hD : depthC α k n ≤ 4 * (32 * α) ^ (k - 2) * n := by
    rw [depthC, sum_range_betaC α (by omega : 1 ≤ k)]
    exact Nat.mul_le_mul_right _ (factIV α k hα hk)
  have h2 : (tree (thetaC α) k (depthC α k n) ψ).length ≤ ∑ j ∈ range ((k - 1) * n / α + 1), (4 * (32 * α) ^ (k - 2) * n).choose j :=
    h1.trans (sum_le_sum fun j _ => Nat.choose_le_choose j hD)
  have hkL : k - 1 ≤ 4 * (32 * α) ^ (k - 2) := by
    have := Nat.lt_pow_self (n := k - 2) (by omega : 1 < 32 * α)
    omega
  exact (Nat.cast_le.2 h2).trans (Thresholds.sum_choose_le_two_rpow hα hkL (log_le_yC hα hk) n)
end SparsificationLemma.Cal
