-- Prove2me | solution 1 for PaddedDescent.F.Mark.inv_layersM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:41.406073+00:00
-- url     : https://prove2.me/submissions/32e5e477-c517-427d-b577-420a8d8ad882

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
import Theorems.Thm_PaddedDescent_F_Mark_inv_replicate
import Theorems.Thm_PaddedDescent_F_Mark_layersM_append

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} (hw : n + 2 ≤ w) (R : ℕ) (ψ : Fml) : Inv n w (layersM n w R ψ) := by
  induction ψ using List.reverseRecOn with
  | nil => exact inv_replicate hw (R + 1)
  | append_singleton ψ C ih => rw [layersM_append]; exact ih.placeM C
end PaddedDescent.F.Mark
