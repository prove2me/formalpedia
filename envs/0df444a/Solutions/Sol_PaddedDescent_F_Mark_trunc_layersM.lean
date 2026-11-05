-- Prove2me | solution 1 for PaddedDescent.F.Mark.trunc_layersM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:24:46.391738+00:00
-- url     : https://prove2.me/submissions/2b997d66-de72-4379-bac5-b287cb879105

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
import Theorems.Thm_PaddedDescent_F_Mark_satL_layersM
import Theorems.Thm_PaddedDescent_F_Mark_good_layersM
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_nvio_eq_zero
import Theorems.Thm_PaddedDescent_F_Mark_trunc_nil_cons
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} (hw : n + 2 ≤ w) {R : ℕ} {ψ : Fml} (hR : 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w) :
    trunc n w ([] :: layersM n w R ψ) = (nSat n ψ : ℤ) := by
  rw [trunc_nil_cons (good_layersM hw hR), nSat]
  congr 2
  refine Finset.filter_congr fun σ _ => ?_
  rw [← nvio_eq_zero]
  exact satL_layersM n w R (ext σ) ψ
end PaddedDescent.F.Mark
