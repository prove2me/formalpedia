-- Prove2me | solution 1 for SplitSat.stCore3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:45:02.692259+00:00
-- url     : https://prove2.me/submissions/3f18dd76-adb4-4ea2-8d31-804f40df016b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic
import Definitions.Def_SplitSat_Procedure
import Theorems.Thm_SplitSat_core3_polyTimeSteps
import Theorems.Thm_SplitSat_core3_decides
import Theorems.Thm_ThreeSatPrinted_algPseudocode_decides_viaC


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight Eight.ViaGrouping GraphProblems
namespace SplitSat
theorem _root_.solution : StCore3 := fun _ hδ => by
  obtain ⟨ℓ, τ, -, -, h⟩ := ThreeSatPrinted.algPseudocode_decides_viaC hδ
  exact ⟨ℓ, τ, core3_polyTimeSteps ℓ τ, core3_decides h⟩
end SplitSat
