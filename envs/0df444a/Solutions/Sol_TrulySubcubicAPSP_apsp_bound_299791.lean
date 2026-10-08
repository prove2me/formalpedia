-- Prove2me | solution 1 for TrulySubcubicAPSP.apsp_bound_299791
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-06T23:51:55.757701+00:00
-- url     : https://prove2.me/submissions/b6c507b3-3efa-4d0e-9dc6-08158f0d7326

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_Problems
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport
import Theorems.Thm_Light_Sec3_apsp_299791

set_option maxHeartbeats 1000000

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution :
    TrulySubcubicAPSP.APSP.SolvedInTime 2.99791 :=
  TrulySubcubicAPSP.sourceSpecificationTransport.2.2 _ Light.Sec3.apsp_299791
