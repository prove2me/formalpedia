-- Prove2me | solution 1 for SatM.targetUniform_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:04:04.680992+00:00
-- url     : https://prove2.me/submissions/c1635f6d-460d-48a5-8ed5-1e97a94ab489

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInKStatement
import Definitions.Def_RecursionWithPieces_Defs
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_RecursionWithPieces_Master
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Top_CaseI
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_SparsifyThenCount_PlanUsed
import Definitions.Def_SparsifyThenCount_Correct
import Definitions.Def_SparsifyThenCount_CorrectB
import Definitions.Def_SparsifyThenCount_Tied
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_VariableBound_Printed_Tied
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_VariableBound_StepParity
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Params_Spec
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_Ev
import Definitions.Def_VariableBound_Count_Correct
import Definitions.Def_VariableBound_Top_Budget
import Definitions.Def_VariableBound_Top_ArithPlan
import Definitions.Def_StepSparsify_WalkCount
import Definitions.Def_StepSparsify_CalServes
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_CorrectB
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_ClauseBound_Both_TimeM
import Definitions.Def_ClauseBound_Alg_TopVal
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_RecursionWithPieces_Main
import Theorems.Thm_RecursionWithPieces_tiedAllCal
import Theorems.Thm_VariableBound_count_of_tied


set_option autoImplicit false
section
section
open SatM
namespace SatM
theorem _root_.solution : TargetUniform :=
  let ⟨_, _, _, _, h⟩ := RecursionWithPieces.tiedAllCal
  VariableBound.count_of_tied h.counts
end SatM
