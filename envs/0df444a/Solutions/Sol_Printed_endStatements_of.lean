-- Prove2me | solution 1 for Printed.endStatements_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:33.432483+00:00
-- url     : https://prove2.me/submissions/9e213bbb-0b4e-4a6d-971c-1ebebaf8f060

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Proof
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Grouping
import Definitions.Def_Variance_Grouping
import Definitions.Def_Exits_End
import Definitions.Def_Value_End
import Definitions.Def_Suffices_Main
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Printed_End
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_eStarZero_from
import Theorems.Thm_Printed_groupingLemma_of
import Theorems.Thm_Printed_levelProposition_from
import Theorems.Thm_Printed_stAlgorithm_of
import Theorems.Thm_Printed_stAnswerEachQuery
import Theorems.Thm_Printed_stClique_from
import Theorems.Thm_Printed_stCountCost_of
import Theorems.Thm_Printed_stDecides_of
import Theorems.Thm_Printed_stEveryEta_from
import Theorems.Thm_Printed_stGroupingPoly
import Theorems.Thm_Printed_stGroupingTied_of
import Theorems.Thm_Printed_stHalf
import Theorems.Thm_Printed_stMono
import Theorems.Thm_Printed_stOnProcedures
import Theorems.Thm_Printed_stProofNamed_of
import Theorems.Thm_Printed_threeSat_by_algorithm_of
import Theorems.Thm_Printed_threeSat_through_eStar_of
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_stMono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (hSearch : Eight.ViaGrouping.StSearch) (hStops : Exits.StSearchStops) (hValue : Value.StValueEqualsZ) (hSuffices : Suffices.StSuffices) (hEnumeration : Enumerate.StEnumeration) : EndStatements :=
  have hG : StGroupingTied := stGroupingTied_of hSearch hStops hValue
  have hC : StClique := stClique_from hG
  have hAlg : StAlgorithm := stAlgorithm_of hSuffices (stCountCost_of hC hG stGroupingPoly stOnProcedures)
  have hDec : StDecides := stDecides_of hAlg hEnumeration
  have hPN : StProofNamed := stProofNamed_of hSuffices hG stGroupingPoly stOnProcedures
  { mono := stMono
    half := stHalf
    answerEachQuery := stAnswerEachQuery
    groupingLemma := groupingLemma_of hG
    levelProposition := levelProposition_from hG
    eStarZero := eStarZero_from hG
    everyEta := stEveryEta_from hG
    clique := hC
    enumeration := hEnumeration
    proofNamed := hPN
    algorithm := hAlg
    decides := hDec
    through_eStar := threeSat_through_eStar_of (stEveryEta_from hG) hEnumeration hPN
    by_algorithm := threeSat_by_algorithm_of hDec }
end Printed
