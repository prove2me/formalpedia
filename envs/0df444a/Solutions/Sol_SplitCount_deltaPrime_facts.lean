-- Prove2me | solution 1 for SplitCount.deltaPrime_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:07:03.684432+00:00
-- url     : https://prove2.me/submissions/fb422e77-7354-4118-ac43-d2f40c81e6c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SplitCount_Main

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace SplitCount
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) {w : ℕ} (hw : 3 ≤ w) (Bl : ℕ) :
    0 < deltaPrime δ w Bl ∧ deltaPrime δ w Bl ≤ 1 ∧ deltaPrime δ w Bl * ((1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3 := by
  have hw' : (3 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hB0 : (0 : ℝ) ≤ (Bl : ℝ) := Nat.cast_nonneg Bl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact mul_pos (by linarith) (by linarith)
  unfold deltaPrime
  rw [← hX]
  refine ⟨lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
  calc min (δ / (3 * X)) 1 * X ≤ δ / (3 * X) * X := mul_le_mul_of_nonneg_right (min_le_left _ _) hX0.le
    _ = δ / 3 := by field_simp
end SplitCount
