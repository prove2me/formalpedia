-- Prove2me | solution 1 for VariableBound.stSearchD
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:21:26.819507+00:00
-- url     : https://prove2.me/submissions/19cc587c-87fb-4b97-99ed-1f2f309f03bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
import Theorems.Thm_VariableBound_Search_fold_inv
import Theorems.Thm_VariableBound_Search_structD_inv
import Theorems.Thm_VariableBound_Search_length_chksD
import Theorems.Thm_VariableBound_stepChoice
set_option autoImplicit false
section
section
open VariableBound
open Groundwork PaddedDescent.F AppVariables Finset

theorem solution : StSearchD := by
  intro X _ m V n nb rb tb pad evX fam hX hnb hrb htb hne hinc hF hev hpad
  have H : Search.Hyp X m n nb rb tb fam := ⟨hX, hnb, hrb, htb, hne, hinc, hF⟩
  obtain ⟨h1, h2⟩ := Search.fold_inv H pad evX hev hpad rb
  refine ⟨Search.structD_inv H _ h1, ?_⟩
  rcases h2 with h2 | h2
  · exact h2
  · have := stepChoice.ends X (Fin m) (Fin fam.length) V n nb rb tb univ (fun i => Fld.setD m (fam.get i)) (chksD m (searchD pad evX fam m nb (beta n m nb) rb tb)) hX hnb
    rw [Fintype.card_fin] at this
    exact this hrb htb hF h1.2 (by rw [Search.length_chksD]; exact h2)
