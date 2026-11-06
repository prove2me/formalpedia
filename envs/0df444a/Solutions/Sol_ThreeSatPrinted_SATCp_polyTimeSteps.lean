-- Prove2me | solution 1 for ThreeSatPrinted.SATCp_polyTimeSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:07.988971+00:00
-- url     : https://prove2.me/submissions/b4a33850-b0a6-43d3-be59-8026fad2a341

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatPrinted_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_Eight_Level_SecPseudocode
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_ThreeSatOnTree_ThmEveryDelta
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Theorems.Thm_ThreeSatPrinted_satC_polyTimeSteps
import Theorems.Thm_Eight_ViaGrouping_COUNTp_polyTimeSteps


set_option autoImplicit false
section
section
open ThreeSatPrinted
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight ThreeSatOnTree
namespace ThreeSatPrinted
theorem _root_.solution (ℓ τ : ℕ) : PolyTimeSteps (SATCp ℓ τ) := satC_polyTimeSteps τ (ViaGrouping.COUNTp_polyTimeSteps ℓ)
end ThreeSatPrinted
