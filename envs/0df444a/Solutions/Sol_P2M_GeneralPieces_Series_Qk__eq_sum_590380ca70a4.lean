-- Prove2me | solution 1 for P2M_GeneralPieces_Series_Qk__eq_sum_590380ca70a4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:52.773503+00:00
-- url     : https://prove2.me/submissions/6a7ac272-dfeb-4134-9c15-f04354deabf7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Theorems.Thm_GeneralPieces_Series_sum_list_comm
import Theorems.Thm_GeneralPieces_Series_sum_range_two_mul
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}
namespace GeneralPieces.Series
theorem _root_.solution (hA : A.Ok b.sum) (s : ℤ) (π σ : Multiset ℕ) : Qk' A b s π σ = (A.map fun c => c.1 * qM c.2 b s π σ).sum := by
  unfold Qk'
  simp only [← List.sum_map_mul_left]
  rw [sum_list_comm]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  rw [qM, ← sum_range_two_mul (h := b.sum) (by have := (hA c hc).2; omega), mul_sum]
  exact sum_congr rfl fun i _ => by ring
end GeneralPieces.Series
