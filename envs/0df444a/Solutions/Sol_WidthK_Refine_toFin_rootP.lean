-- Prove2me | solution 1 for WidthK.Refine.toFin_rootP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:44:30.671132+00:00
-- url     : https://prove2.me/submissions/8c0213b4-81a0-4bab-9c02-f68c51884055

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_toFinset_rootP
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution (ψ : PFml) : toFin (rootP ψ) = red (toFin ψ) := toFinset_rootP ψ
end WidthK.Refine
