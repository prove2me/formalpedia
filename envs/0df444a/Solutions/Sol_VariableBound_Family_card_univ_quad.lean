-- Prove2me | solution 1 for VariableBound.Family.card_univ_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:05:15.944032+00:00
-- url     : https://prove2.me/submissions/11caf795-32fd-42ba-9d7f-e9e3d9c169a6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main

set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
namespace VariableBound.Family
theorem _root_.solution : #(univ : Finset (F × F × F × F)) = Fintype.card F ^ 4 := by
  simp only [card_univ, Fintype.card_prod]
  ring
end VariableBound.Family
