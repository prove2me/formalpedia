-- Prove2me | solution 1 for Sat3.inRateTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:58.763787+00:00
-- url     : https://prove2.me/submissions/53fe94d2-855f-4a77-8d92-619dd438b44a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_Reduce
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_PaddedDescent_F_Expand
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_MarkLayers
import Definitions.Def_PaddedDescent_F_MarkCode
import Definitions.Def_PaddedDescent_F_MarkVal
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkSum
import Definitions.Def_PaddedDescent_F_MarkSize
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_ArithSched
import Definitions.Def_PaddedDescent_F_ArithA
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertSide
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_PaddedDescent_F_CertA
import Definitions.Def_PaddedDescent_Main
import Theorems.Thm_PaddedDescent_F_CertGrid_certBrute
import Theorems.Thm_PaddedDescent_F_CertGrid_certExpand
import Theorems.Thm_PaddedDescent_F_CertTop_certA
import Theorems.Thm_PaddedDescent_F_Eval_stCountM
import Theorems.Thm_PaddedDescent_F_Eval_stEval
import Theorems.Thm_PaddedDescent_F_Eval_stValF
import Theorems.Thm_PaddedDescent_F_Expand_stE
import Theorems.Thm_PaddedDescent_F_Mark_Pi_stPiSum
import Theorems.Thm_PaddedDescent_F_Mark_Prof_stProfSum
import Theorems.Thm_PaddedDescent_F_Mark_Sum_stMarkSum
import Theorems.Thm_PaddedDescent_F_Mark_Val_stMarkPresents
import Theorems.Thm_PaddedDescent_F_Mark_Val_stMarkVal
import Theorems.Thm_PaddedDescent_F_RebalF_stR
import Theorems.Thm_PaddedDescent_F_Table_stT3b
import Theorems.Thm_PaddedDescent_F_Top_correct
import Theorems.Thm_PaddedDescent_F_certAdm
import Theorems.Thm_PaddedDescent_F_certDescend
import Theorems.Thm_PaddedDescent_F_certMark
import Theorems.Thm_PaddedDescent_F_certRebal
import Theorems.Thm_PaddedDescent_F_certRebalG
import Theorems.Thm_PaddedDescent_F_stA
import Theorems.Thm_PaddedDescent_F_stAW
import Theorems.Thm_PaddedDescent_F_stCertSide
import Theorems.Thm_PaddedDescent_F_stD
import Theorems.Thm_PaddedDescent_F_stEncInj
import Theorems.Thm_PaddedDescent_F_stEncLen
import Theorems.Thm_PaddedDescent_F_stLayersE
import Theorems.Thm_PaddedDescent_F_stLeaf
import Theorems.Thm_PaddedDescent_F_stMarkSized
import Theorems.Thm_PaddedDescent_F_stSched
import Theorems.Thm_PaddedDescent_inRateTM_of_algorithm
import Theorems.Thm_PaddedDescent_two_pow_s0K_le


set_option autoImplicit false
section
open Sat3
open PaddedDescent PaddedDescent.F
namespace Sat3
theorem _root_.solution : InRateTM (3 / 19) :=
  inRateTM_of_algorithm (C0K 3) (s0K 3) (two_pow_s0K_le 3)
    (CertTop.certA certRebal (certDescend (CertGrid.certExpand certRebalG stCertSide)) CertGrid.certBrute certMark certAdm)
    (Top.correct
      (Eval.stCountM
        (Eval.stEval (Eval.stValF RebalF.stR (stD Table.stT3b Expand.stE)) Mark.Val.stMarkPresents
          (Mark.Sum.stMarkSum (Mark.Val.stMarkVal stEncLen stEncInj) Mark.Prof.stProfSum Mark.Pi.stPiSum) stMarkSized)
        stLayersE)
      stLeaf stSched stA stAW)
end Sat3
