-- Prove2me | solution 1 for SatFree.increasing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:42:06.886361+00:00
-- url     : https://prove2.me/submissions/ccb5f379-5c3a-4f98-8bce-b5582007d91b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Order
import Theorems.Thm_SatFree_sameMachine

set_option autoImplicit false
section
section
open SatFree
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : Increasing := fun k =>
  le_iInf₂ fun δ hδ => iInf₂_le δ (by
    obtain ⟨M, c, hfin, h⟩ := hδ
    exact ⟨M, c, hfin, sameMachine k M _ h⟩)
end SatFree
