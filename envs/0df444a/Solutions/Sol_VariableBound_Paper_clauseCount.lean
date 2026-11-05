-- Prove2me | solution 1 for VariableBound.Paper.clauseCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:39:13.936226+00:00
-- url     : https://prove2.me/submissions/d0b73eee-33b1-4b0e-b126-ad6a621908e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Sat3_Is3CNF_length_le


set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)
namespace VariableBound.Paper
theorem _root_.solution : ClauseCountStmt := fun _ _ _ h => Groundwork.DecodeK.IsKCNF.length_le h
end VariableBound.Paper
