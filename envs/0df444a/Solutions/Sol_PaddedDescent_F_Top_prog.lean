-- Prove2me | solution 1 for PaddedDescent.F.Top.prog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:32:49.798964+00:00
-- url     : https://prove2.me/submissions/a115b6d1-9cea-4d65-b34c-1d0731e5dbe6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_WidthK_Refine_stRefines
import Theorems.Thm_WidthK_stBetaSum
import Theorems.Thm_WidthK_stHeavyEq
import Theorems.Thm_WidthK_stLeafCard
import Theorems.Thm_WidthK_stLightEq
import Theorems.Thm_WidthK_stNodeBound
import Theorems.Thm_WidthK_stNodeRoot
import Theorems.Thm_WidthK_stNodeStep
import Theorems.Thm_WidthK_stProg
import Theorems.Thm_WidthK_stSatIff
import Theorems.Thm_WidthK_stThr


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace PaddedDescent.F.Top
theorem _root_.solution : WidthK.StProg :=
  WidthK.stProg WidthK.stNodeRoot WidthK.stNodeStep WidthK.stNodeBound WidthK.stLeafCard WidthK.stLightEq WidthK.stHeavyEq
    WidthK.stSatIff WidthK.stThr WidthK.stBetaSum WidthK.Refine.stRefines
end PaddedDescent.F.Top
