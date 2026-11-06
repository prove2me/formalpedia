-- Prove2me | solution 1 for RecursionWithPieces.Forms.thmVariablesB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:17:55.24671+00:00
-- url     : https://prove2.me/submissions/71ef04dd-3c94-46e1-b7a0-e5623986af35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_RecursionWithPieces_Forms
import Theorems.Thm_RecursionWithPieces_Forms_togetherAllOccur

set_option autoImplicit false
section
section
open RecursionWithPieces RecursionWithPieces.Forms
open MainTheoremForms VariableBound.Paper RecursionWithPieces
namespace RecursionWithPieces.Forms
theorem _root_.solution : ThmVariablesB :=
  let ⟨M, C, hfin, _, h, _⟩ := togetherAllOccur
  ⟨M, C, hfin, h⟩
end RecursionWithPieces.Forms
