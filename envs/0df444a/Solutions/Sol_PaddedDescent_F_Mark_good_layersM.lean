-- Prove2me | solution 1 for PaddedDescent.F.Mark.good_layersM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:22.727424+00:00
-- url     : https://prove2.me/submissions/f2d724e3-be8c-461b-b24e-3ba886eb9f7f

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
import Theorems.Thm_PaddedDescent_F_Mark_Inv_good
import Theorems.Thm_PaddedDescent_F_Mark_inv_layersM
import Theorems.Thm_PaddedDescent_F_Mark_last_layersM_le
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} (hw : n + 2 ≤ w) {R : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w) :
    Good n w (layersM n w R ψ) := (inv_layersM hw R ψ).good (last_layersM_le hw hR)
end PaddedDescent.F.Mark
