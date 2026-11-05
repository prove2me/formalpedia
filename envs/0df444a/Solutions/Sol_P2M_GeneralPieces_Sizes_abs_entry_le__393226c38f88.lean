-- Prove2me | solution 1 for P2M_GeneralPieces_Sizes_abs_entry_le__393226c38f88
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:08.303938+00:00
-- url     : https://prove2.me/submissions/726c1743-1782-4218-95d3-55522d0b0940

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_length_le
import Theorems.Thm_GeneralPieces_Sizes_abs_entry_le
import Theorems.Thm_GeneralPieces_Sizes_pow_le
import Theorems.Thm_ClauseBound_Boson_Size_le_sum_of_mem
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) (a : List ℕ+) (ha : (toL a).sum ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (opMon a r (tpow σ))| ≤ 2 ^ (12 * h ^ 2) := by
  have a1 : ∀ n ∈ a, (n : ℕ) ≤ h := fun n hn => (List.le_sum_of_mem (List.mem_map_of_mem hn : (n : ℕ) ∈ toL a)).trans ha
  have a2 : (1 : ℚ) ≤ 32 * (h : ℚ) ^ 2 * 2 ^ (5 * h) := by
    have : 1 ≤ 32 * h ^ 2 * 2 ^ (5 * h) := Nat.succ_le_of_lt (by positivity)
    exact_mod_cast this
  calc _ ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length := abs_entry_le hh a a1 r h1 h2
    _ ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ h := pow_le_pow_right₀ a2 ((length_le a).trans ha)
    _ ≤ 2 ^ (12 * h ^ 2) := by exact_mod_cast pow_le hh
end GeneralPieces.Sizes
