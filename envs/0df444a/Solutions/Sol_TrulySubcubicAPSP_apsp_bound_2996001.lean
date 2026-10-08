-- Prove2me | solution 1 for TrulySubcubicAPSP.apsp_bound_2996001
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T06:44:43.152518+00:00
-- url     : https://prove2.me/submissions/c3099432-01ba-4181-b058-ef0e51b07f3b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_Problems
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport
import Theorems.Thm_Light_Filter_apsp_2996001

set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.996001 :=
  TrulySubcubicAPSP.sourceSpecificationTransport.2.2 _ Light.Filter.apsp_2996001
