-- Prove2me | solution 1 for VariableBound.Paper.together_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:03.592962+00:00
-- url     : https://prove2.me/submissions/c1057f6f-3f93-4293-acb6-bdbfc0f7f775

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
import Theorems.Thm_VariableBound_Paper_corMinIsMainTheorem
import Theorems.Thm_VariableBound_Paper_thmVariablesBFor_of
import Theorems.Thm_VariableBound_Paper_mainTheoremFor_of

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)
namespace VariableBound.Paper
theorem _root_.solution (h : SatM.TargetUniform) : TogetherAllOccur := by
  obtain ⟨M, C, hfin, hN, -, hB⟩ := h
  have h2 : MainTheoremFor M (3 * C) := mainTheoremFor_of hB
  exact ⟨M, 3 * C, hfin, h2, thmVariablesBFor_of hN, (corMinIsMainTheorem M (3 * C)).2 h2⟩
end VariableBound.Paper
