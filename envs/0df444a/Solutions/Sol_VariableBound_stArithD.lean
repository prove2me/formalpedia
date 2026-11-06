-- Prove2me | solution 1 for VariableBound.stArithD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:06:16.732256+00:00
-- url     : https://prove2.me/submissions/1e31eff5-b76f-48de-b0ac-a60f714f8d41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_VariableBound_Top_ArithNeed
import Definitions.Def_VariableBound_Top_ArithPlan
import Definitions.Def_VariableBound_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Top_Arith
import Theorems.Thm_UniformInK_stBetaU
import Theorems.Thm_UniformInK_stDLogU
import Theorems.Thm_UniformInK_stMasterU
import Theorems.Thm_UniformInK_stSixU
import Theorems.Thm_VariableBound_Arith_stArithD_of
import Theorems.Thm_VariableBound_stArgD
import Theorems.Thm_VariableBound_stLowerD
import Theorems.Thm_VariableBound_stNeedD
import Theorems.Thm_VariableBound_stPlanLeD
import Theorems.Thm_VariableBound_stPlanNeedD
import Theorems.Thm_VariableBound_stUbD


set_option autoImplicit false
section
open VariableBound
open UniformInK
namespace VariableBound
theorem _root_.solution (hB : Net.StBounds) : StArithD :=
  Arith.stArithD_of (stNeedD (stUbD hB) (stArgD hB) (stLowerD hB) stBetaU) stPlanLeD stPlanNeedD stMasterU stDLogU stSixU stBetaU
end VariableBound
