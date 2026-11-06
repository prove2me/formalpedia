-- Prove2me | solution 1 for VariableBound.Net.SizeP.sum_home_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:34.790352+00:00
-- url     : https://prove2.me/submissions/23cfcc2d-c0d0-4fa5-bf84-42e7bab5dce8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_VariableBound_Net_SizeP_card_home_le
import Theorems.Thm_VariableBound_Net_SizeP_qv_mono
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Net_Basic_getD_mem
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution (hg : 0 < g) {rb : ℕ} {sb : ℚ} (hsb : 0 ≤ sb) (hr : D.2.length ≤ rb) (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (a : ℕ) :
    ((∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length : ℕ) : ℚ) ≤ (qv g rb : ℚ) * sb := by
  push_cast
  calc ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), ((D.2.getD j []).length : ℚ)
      ≤ ∑ _j ∈ (range D.2.length).filter (fun j => home g j = a), sb :=
        sum_le_sum fun j hj => hs _ (Basic.getD_mem (mem_range.1 (mem_filter.1 hj).1))
    _ = (#((range D.2.length).filter fun j => home g j = a) : ℚ) * sb := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (qv g rb : ℚ) * sb := by
        refine mul_le_mul_of_nonneg_right ?_ hsb
        exact_mod_cast (card_home_le hg _ a).trans (qv_mono hr)
end VariableBound.Net.SizeP
