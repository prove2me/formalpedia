-- Prove2me | solution 1 for VariableBound.Net.SizeP.bits_le_P0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:08:46.920549+00:00
-- url     : https://prove2.me/submissions/35ba82ca-0f23-4a2e-bc59-7ecafadaf2df

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
import Theorems.Thm_VariableBound_Net_SizeP_length_tch_le
import Theorems.Thm_VariableBound_Net_SizeP_sum_home_le
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le
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
theorem _root_.solution (hg : 0 < g) {tb rb : ℕ} {sb : ℚ} (hsb : 0 ≤ sb) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (hr : D.2.length ≤ rb)
    (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (hc : ∀ e < D.1.length, colD D e ≤ tb + 2) (a : ℕ) :
    ((qv g n + (tch g n D a).length : ℕ) : ℚ) ≤ P0 g n Δ tb rb sb := by
  have h1 : ((tch g n D a).length : ℚ) ≤
      ((qv g n * Δ * (1 + (tb + 2)) + ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length : ℕ) : ℚ) := by
    exact_mod_cast length_tch_le hg hW hΔ hc a
  have h2 := sum_home_le hg hsb hr hs a
  rw [Nat.cast_add] at h1
  unfold P0
  push_cast at h1 h2 ⊢
  nlinarith [h1, h2]
end VariableBound.Net.SizeP
