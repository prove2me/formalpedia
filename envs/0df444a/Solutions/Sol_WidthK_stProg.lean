-- Prove2me | solution 1 for WidthK.stProg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:36:31.49662+00:00
-- url     : https://prove2.me/submissions/140a85b4-3964-4608-853c-2292923b8156

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_ProgMain_sparsify_prog_of
import Theorems.Thm_WidthK_ProgMain_iface
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open WidthK
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK
theorem _root_.solution (h1 : StNodeRoot) (h2 : StNodeStep) (h3 : StNodeBound) (h4 : StLeafCard) (h5 : StLightEq) (h6 : StHeavyEq) (h7 : StSatIff)
    (h8 : StThr) (h9 : StBetaSum) (h10 : StRefines) : StProg := by
  intro τ k n hτ ψ hψ
  refine ProgMain.sparsify_prog_of (ProgMain.iface h1 h2 h3 h4 h5 h6 h7 h8 h9 hτ k n) (h10 _ k (h8 τ hτ).pos) (n := n) (hv := k * n / τ)
    ?_ ψ ?_ fun C hC => (hψ C hC).2
  · calc k * n < τ * (k * n / τ + 1) := Nat.lt_mul_div_succ (k * n) (by omega : 0 < τ)
      _ = (k * n / τ + 1) * τ := Nat.mul_comm _ _
  · intro X hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
end WidthK
