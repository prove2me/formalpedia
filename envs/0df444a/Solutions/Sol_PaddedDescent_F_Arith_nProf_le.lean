-- Prove2me | solution 1 for PaddedDescent.F.Arith.nProf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:31.406245+00:00
-- url     : https://prove2.me/submissions/b3a3ad17-ffd6-49b5-80c0-3b0bca2e59fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark
import Theorems.Thm_PaddedDescent_F_Arith_clauses_succ_le
import Theorems.Thm_PaddedDescent_F_Arith_prof_exponent_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent
namespace PaddedDescent.F.Arith
theorem _root_.solution {Δ n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) (hΔ : Δ ≤ 2 ^ betaOf (sOf n)) :
    Mark.nProf (3 * Kseq (depthOf (sOf n)) ^ 8) (Δ * n) (layersOf (sOf n) + 2) ≤ F := by
  have hg : 3 * Kseq (depthOf (sOf n)) ^ 8 * (3 * Kseq (depthOf (sOf n)) ^ 8) = Ytop (sOf n) := by
    rw [Ytop, gtop, Ktop, sq]
  have h1 := prof_exponent_le hs
  unfold Mark.nProf
  rw [hg]
  calc (Δ * n + 1) ^ (Ytop (sOf n) * (layersOf (sOf n) + 2))
      ≤ (2 ^ (betaOf (sOf n) + Nat.size n)) ^ (Ytop (sOf n) * (layersOf (sOf n) + 2)) :=
        Nat.pow_le_pow_left (clauses_succ_le hΔ _) _
    _ = 2 ^ ((betaOf (sOf n) + Nat.size n) * (Ytop (sOf n) * (layersOf (sOf n) + 2))) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) := Nat.pow_le_pow_right (by norm_num) (h1.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hC)))
    _ ≤ F := hF
end PaddedDescent.F.Arith
