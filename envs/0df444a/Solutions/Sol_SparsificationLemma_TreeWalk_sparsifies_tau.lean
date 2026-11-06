-- Prove2me | solution 1 for SparsificationLemma.TreeWalk.sparsifies_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:37:32.557203+00:00
-- url     : https://prove2.me/submissions/7e04af27-8358-4b4d-b792-db7ce24508fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Theorems.Thm_SparsificationLemma_TreeWalk_iface
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Gen_ok_of
import Theorems.Thm_SparsificationLemma_Geo_le_bsumU
import Theorems.Thm_SparsificationLemma_Geo_stThrGeo
import Theorems.Thm_UniformInK_Leaves_le_bsumU
import Theorems.Thm_WidthK_ProgMain_iface
import Theorems.Thm_WidthK_ProgMain_sparsify_prog_of
import Theorems.Thm_WidthK_Refine_stRefines
import Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}
namespace SparsificationLemma.TreeWalk
theorem _root_.solution {ε : ℝ} (hk : 1 ≤ k) (hτ : 8 * k ≤ τ)
    (hε : ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ k : ℝ)) ≤ ε) :
    Sparsifies k ε (stepK (thetaU τ) k) rootP (bsumU τ k) (leafCU τ k) (2 ^ k) := by
  intro n ψ hψ
  have hT : (k - 1) * n < ((k - 1) * n / τ + 1) * τ := by
    calc (k - 1) * n < τ * ((k - 1) * n / τ + 1) := Nat.lt_mul_div_succ _ (by omega : 0 < τ)
      _ = ((k - 1) * n / τ + 1) * τ := Nat.mul_comm _ _
  obtain ⟨c1, c2, c3, c4⟩ := ProgMain.sparsify_prog_of (iface hk hτ n) (Refine.stRefines _ k (stThrGeo k τ hk hτ).pos) hT ψ (Gen.ok_of hψ)
    fun C hC => (hψ C hC).2
  refine ⟨?_, c2, c3, c4⟩
  have h1 : ∑ j ∈ range ((k - 1) * n / τ + 1), (bsumU τ k * n).choose j ≤ ∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j :=
    sum_le_sum_of_subset (range_mono (Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le k 1)))))
  calc ((leaves (stepK (thetaU τ) k) (bsumU τ k * n) (rootP ψ)).length : ℝ)
      ≤ ((∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j : ℕ) : ℝ) := by exact_mod_cast c1.trans h1
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := Thresholds.sum_choose_le_two_rpow (by omega) (le_bsumU (by omega)) hε n
end SparsificationLemma.TreeWalk
