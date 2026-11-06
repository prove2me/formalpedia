-- Prove2me | solution 1 for Variance.groupingFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:08.483598+00:00
-- url     : https://prove2.me/submissions/b5d15255-9263-4223-8934-82ff97e6ea40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Var
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_Eight_SecNetworks_Grouping
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Grouping
import Theorems.Thm_Variance_stTotalLe
import Theorems.Thm_Variance_stChebOfVar
import Theorems.Thm_Variance_stSomePairOfCheb
import Theorems.Thm_Variance_stGroupingOf
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Variance_stVar
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
namespace Variance
theorem _root_.solution : GroupingFacts := stGroupingOf stVar stTotalLe stChebOfVar stSomePairOfCheb
end Variance
