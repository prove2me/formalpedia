-- Prove2me | solution 1 for TrulySubcubicAPSP.apsp_bound_2995561
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T15:26:25.029776+00:00
-- url     : https://prove2.me/submissions/c5e2e28f-d852-4f6d-a8c3-90d9a44f4ac7

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_Problems
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport
import Theorems.Thm_apsp_2995561

set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.995561 :=
  TrulySubcubicAPSP.sourceSpecificationTransport.2.2 _ apsp_2995561
