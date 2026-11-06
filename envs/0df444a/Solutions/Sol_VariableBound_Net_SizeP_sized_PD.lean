-- Prove2me | solution 1 for VariableBound.Net.SizeP.sized_PD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:06.577201+00:00
-- url     : https://prove2.me/submissions/2c0601a4-215c-4380-a412-cbe83d17275b

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
import Theorems.Thm_VariableBound_Net_SizeP_sized_netDN
import Theorems.Thm_VariableBound_Net_SizeP_bits_le_P0
import Theorems.Thm_VariableBound_Net_SizeP_le_PD
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution (hg : 0 < g) {tb rb B y : ℕ} {sb : ℚ} {fl : Bool} (hsb : 0 ≤ sb) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) (hr : D.2.length ≤ rb)
    (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (hc : ∀ e < D.1.length, colD D e ≤ tb + 2) (h3 : ∀ a < g, ∀ z, |WD g n D y fl a z| ≤ 2 ^ B) :
    (netDN g (ctx g n D y fl)).Sized (PD g n Δ tb rb sb) B := by
  refine sized_netDN (fun a _ => le_PD ?_) (fun a _ => le_PD ?_) h3
  · have h := bits_le_P0 hg hsb hW hΔ hr hs hc a
    have h0 : (0 : ℚ) ≤ ((qv g n + (tch g n D a).length : ℕ) : ℚ) := Nat.cast_nonneg _
    linarith
  · have h := bits_le_P0 hg hsb hW hΔ hr hs hc a
    push_cast at h ⊢
    have h0 : (0 : ℚ) ≤ (qv g n : ℚ) := Nat.cast_nonneg _
    linarith
end VariableBound.Net.SizeP
