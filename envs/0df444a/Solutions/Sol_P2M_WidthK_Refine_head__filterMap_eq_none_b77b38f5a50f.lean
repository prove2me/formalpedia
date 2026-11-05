-- Prove2me | solution 1 for P2M_WidthK_Refine_head__filterMap_eq_none_b77b38f5a50f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:21:52.889334+00:00
-- url     : https://prove2.me/submissions/3f7b7e44-76f6-4727-9b69-f7af027b0f9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filterMap
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filterMap



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {α β : Type*} {f : α → Option β} {l : List α}
    (h : (l.filterMap f).head? = none) : ∀ x ∈ l, f x = none := by
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
  exact h
end WidthK.Refine
