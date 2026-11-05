-- Prove2me | solution 1 for WidthK.Refine.NF_rootP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:21:54.149194+00:00
-- url     : https://prove2.me/submissions/640b9c28-6f07-49ae-ab9c-eaeef33e32db

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_nodeP_root
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution (ψ : PFml) : NF (rootP ψ) := by
  have h := nodeP_root 0 ψ
  exact ⟨h.1, h.2.1⟩
end WidthK.Refine
