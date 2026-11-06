-- Prove2me | solution 1 for SparsificationLemma.Geo.stThmTau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:05.387182+00:00
-- url     : https://prove2.me/submissions/233e19d1-acf0-4ab6-bade-ab77b7ef9dc8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsificationLemma_Geo_Tau
import Theorems.Thm_SparsificationLemma_Geo_le_bsumU
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Geo_stDegGeo
import Theorems.Thm_SparsificationLemma_Geo_stThrGeo
import Theorems.Thm_SparsificationLemma_stExactlyOne
import Theorems.Thm_SparsificationLemma_stGen
import Theorems.Thm_SparsificationLemma_stNodup
import Theorems.Thm_SparsificationLemma_stSide
import Theorems.Thm_UniformInK_Leaves_le_bsumU
import Theorems.Thm_UniformInK_stBetaSumU
import Theorems.Thm_WidthK_Thresholds_sum_choose_le_two_rpow
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK
namespace SparsificationLemma.Geo
theorem _root_.solution : StThmTau := by
  intro k n τ ε φ hk hτ hε hφ
  have hτ2 : 2 ≤ τ := by omega
  obtain ⟨g1, g2, g3, -⟩ := stGen stSide k τ n (bsumU τ k * n) (thetaU τ) (betaSU τ) hk (by omega) (stThrGeo k τ hk hτ)
    (Nat.mul_le_mul_right _ (stBetaSumU τ k hτ2)) φ hφ
  refine ⟨g1, fun Φ hΦ => ⟨(g3 Φ hΦ).1, stNodup _ _ _ _ Φ hΦ⟩, ?_, fun b => stExactlyOne _ _ _ _ b, fun Φ hΦ v => ((g3 Φ hΦ).2 v).trans (stDegGeo k τ hk (by omega))⟩
  have h1 : ∑ j ∈ range ((k - 1) * n / τ + 1), (bsumU τ k * n).choose j ≤ ∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j :=
    sum_le_sum_of_subset (range_mono (Nat.succ_le_succ (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le k 1)))))
  calc ((outTau k n τ φ).length : ℝ) ≤ ((∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j : ℕ) : ℝ) := by exact_mod_cast g2.trans h1
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := WidthK.Thresholds.sum_choose_le_two_rpow (by omega) (le_bsumU hτ2) hε n
end SparsificationLemma.Geo
