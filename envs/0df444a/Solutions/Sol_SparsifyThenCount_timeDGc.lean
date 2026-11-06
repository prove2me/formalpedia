-- Prove2me | solution 1 for SparsifyThenCount.timeDGc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:41:15.277976+00:00
-- url     : https://prove2.me/submissions/2d3922fa-3bfb-4937-8b9e-8579441fe080

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_SparsifyThenCount_Correct
import Definitions.Def_SparsifyThenCount_CorrectB
import Definitions.Def_SparsifyThenCount_CertTop
import Definitions.Def_SparsifyThenCount_CertBoth
import Definitions.Def_SparsifyThenCount_Tied
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_VariableBound_Printed_Tied
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Top_Time
import Definitions.Def_VariableBound_Top_Budget
import Definitions.Def_VariableBound_Top_CorrectB
import Definitions.Def_VariableBound_Top_Arith
import Definitions.Def_VariableBound_Top_ArithPlan
import Definitions.Def_StepSparsify_WalkCount
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_StepSparsify_CalServes
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_CorrectB
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_SparsifyThenCount_Main
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_VariableBound_arithDc
import Theorems.Thm_VariableBound_stPlanLeD
import Theorems.Thm_VariableBound_stTimeD


set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks ClauseBound.TopN UniformInK VariableBound VariableBound.Decide
namespace SparsifyThenCount
theorem _root_.solution : StTimeD := stTimeD arithDc stPlanLeD Decode.stDecM
end SparsifyThenCount
