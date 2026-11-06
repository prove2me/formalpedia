-- Prove2me | solution 1 for VariableBound.Net.SizeP.stSized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:40.085674+00:00
-- url     : https://prove2.me/submissions/1e6bf15f-a8ab-40f6-a0e7-886f8d576740

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
import Theorems.Thm_VariableBound_Net_SizeP_sized_PD
import Theorems.Thm_VariableBound_Net_SizeB_abs_WD_le


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution : StSized := fun _ _ _ _ _ _ _ _ _ _ _ _ hg hsb hW hΔ hr hs hc hadm =>
  sized_PD hg hsb hW hΔ hr hs hc fun _ ha z => SizeB.abs_WD_le hg hW hadm ha z
end VariableBound.Net.SizeP
