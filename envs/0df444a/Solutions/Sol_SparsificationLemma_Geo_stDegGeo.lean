-- Prove2me | solution 1 for SparsificationLemma.Geo.stDegGeo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:38.245838+00:00
-- url     : https://prove2.me/submissions/e42e7f36-b315-487b-94bd-54b2c09de65c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Bound
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_SparsificationLemma_Geo_Thr
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_UniformInK_Budget_leafCU_add_two_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset UniformInK
namespace SparsificationLemma.Geo
theorem _root_.solution : StDegGeo := fun _ _ hk hτ => Budget.leafCU_add_two_le hτ hk
end SparsificationLemma.Geo
