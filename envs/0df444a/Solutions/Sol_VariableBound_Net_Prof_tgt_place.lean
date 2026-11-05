-- Prove2me | solution 1 for VariableBound.Net.Prof.tgt_place
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:49:10.21362+00:00
-- url     : https://prove2.me/submissions/a493ad01-e96a-4402-a3d6-19454a0e0ad5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_PaddedDescent_F_Mark_Prof_place_dec


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {g n : ℕ} {D : Dat} (P : Finset ℕ) {a b κ : ℕ} (hb : b < g) (hκ : κ < 2) :
    tgt g n D P ((a * g + b) * 2 + κ) = if b < a then 0 else if a = b then oc g n D P a κ else pw g n D P a b κ := by
  obtain ⟨d1, d2, d3⟩ := Mark.Prof.place_dec (A := a) hb hκ
  unfold tgt
  rw [d1, d2, d3]
end VariableBound.Net.Prof
