-- Prove2me | solution 1 for PaddedDescent.F.SideF.stChild
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:31.535113+00:00
-- url     : https://prove2.me/submissions/ee0ff78c-1f69-435c-aeec-70bbba2b794e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
import Theorems.Thm_PaddedDescent_F_SideF_stS
import Theorems.Thm_PaddedDescent_F_SideF_Pn_mono
import Theorems.Thm_PaddedDescent_F_SideF_lamNext_mono
import Theorems.Thm_PaddedDescent_F_SideF_bNext_mono
import Theorems.Thm_PaddedDescent_F_SideF_le_mul_div_succ
import Theorems.Thm_Groundwork_Grid_sideCap_le
import Theorems.Thm_Groundwork_Grid_sideN_c
import Theorems.Thm_Groundwork_Grid_sideN_sized
import Theorems.Thm_Groundwork_Grid_value_sideN
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Price_U_side_le
import Theorems.Thm_PaddedDescent_F_RebalF_pos_of_colOK
import Theorems.Thm_PaddedDescent_F_RebalF_stRG
import Theorems.Thm_PaddedDescent_F_Table_stT3c
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.SideF
theorem _root_.solution : StChild := by
  intro pad L Λ B I y hK hcol hI hb _
  have hℓ1 : 1 ≤ I.1.length := hI.lam_pos
  have hℓΛ : I.1.length ≤ Λ := hI.lam_le
  have hg0 : 0 < L.2.length := RebalF.pos_of_colOK (by omega) hcol
  have two : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h => Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨tr, htr⟩ : ∃ tr, tr = decide (priceCol L.2.length I.1.length y < priceRow L.2.length I.1.length y) := ⟨_, rfl⟩
  have hU : (sideN L.2.length tr I.1.length (instOf (K := L.2.length * L.2.length) I.2) y).U ≤ Ubar L.2.length I.1.length := by
    rw [htr]; exact Price.U_side_le _ _ _ _
  have hlam : 2 ^ I.1.length ≤ pad.length := by
    refine (two ?_).trans hb.lab
    have h1 : 1 ≤ 2 * L.2.length ^ 3 := by
      have := Nat.pow_pos (n := 3) hg0
      omega
    calc I.1.length ≤ Λ := hℓΛ
      _ = 1 * Λ := (Nat.one_mul _).symm
      _ ≤ Pn L.2.length Λ := Nat.mul_le_mul_right _ h1
  have hN := stS pad L.2 tr I.1 y I.2 hlam
  have hS := sideN_sized tr hℓ1 (Table.stT3c _ _ _ _ hI) y
  have hD0 : 0 < Dcol * L.1.length ^ 2 := by
    have : 0 < Dcol := by unfold Dcol; positivity
    positivity
  have hM0 : 0 < capM L.2.length I.1.length := by unfold capM; positivity
  have hβ : Dcol * (sideN L.2.length tr I.1.length (instOf (K := L.2.length * L.2.length) I.2) y).U +
      3 * L.2.length ^ 2 * capM L.2.length I.1.length ≤ Dcol * L.1.length ^ 2 * lamNext L.1.length L.2.length I.1.length :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hU) _).trans (le_mul_div_succ _ hD0)
  obtain ⟨J, h1, h2, h3, h4⟩ := RebalF.stRG _ pad L.1.length L.2.length (lamNext L.1.length L.2.length I.1.length) sideF
    ((pad, L.2, tr), (I.1, y, I.2)) _ _ _ (capM L.2.length I.1.length) hK hcol hN hS hM0
    (fun a b hab => by rw [sideN_c _ _ _ _ _ hab]; exact sideCap_le tr hℓ1 y a b) (Nat.le_add_left 1 _) hβ hb.col
    ((two (Nat.mul_le_mul_right _ (Pn_mono hℓΛ))).trans hb.st) ((two (Pn_mono hℓΛ)).trans hb.lab)
    ((two (Nat.mul_le_mul_left _ (lamNext_mono hℓΛ))).trans hb.tab)
  refine ⟨J, ?_, by rw [h2, value_sideN], ?_⟩
  · unfold childF sideCtx
    rw [← htr]
    exact h1
  · exact ⟨h4.lam_pos, h4.lam_le.trans (lamNext_mono hℓΛ), h4.rows, h4.row_len,
      fun r hr z hz => (h4.abs_le r hr z hz).trans (two (bNext_mono hℓΛ))⟩
end PaddedDescent.F.SideF
