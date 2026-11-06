-- Prove2me | solution 1 for Variance.stSearch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:27:18.126813+00:00
-- url     : https://prove2.me/submissions/8e4e6ae7-5221-4a4b-b700-bcdf3acd1338

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
import Theorems.Thm_Variance_groupingFacts
import Theorems.Thm_Variance_stSearchOfGrouping
import Theorems.Thm_Eight_SecNetworks_groupingFacts
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping
namespace Variance
theorem _root_.solution : Eight.ViaGrouping.StSearch := stSearchOfGrouping Variance.groupingFacts
end Variance
