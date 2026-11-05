-- Prove2me | solution 1 for PaddedDescent.F.Mark.last_layersM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:53.250892+00:00
-- url     : https://prove2.me/submissions/72ac292c-19b2-4703-ae1a-8eac5bbbd2cf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_PaddedDescent_F_Mark_Inv_last_le
import Theorems.Thm_PaddedDescent_F_Mark_length_layersM
import Theorems.Thm_PaddedDescent_F_Mark_layersM_ne_nil
import Theorems.Thm_PaddedDescent_F_Mark_inv_layersM
import Theorems.Thm_PaddedDescent_F_Mark_length_flatten_layersM
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} (hw : n + 2 ≤ w) {R c : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * c) :
    ((layersM n w R ψ).getLastD []).length ≤ c := by
  have h := (inv_layersM hw R ψ).last_le (layersM_ne_nil n w R ψ)
  rw [length_layersM, Nat.add_sub_cancel, length_flatten_layersM] at h
  have h2 : 3 ^ R * ((layersM n w R ψ).getLastD []).length ≤ 3 ^ R * c := by omega
  exact Nat.le_of_mul_le_mul_left h2 (by positivity)
end PaddedDescent.F.Mark
