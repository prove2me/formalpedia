-- Prove2me | solution 1 for WidthK.Refine.maskP_sublist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:19:14.930286+00:00
-- url     : https://prove2.me/submissions/83e29105-0377-4c85-830b-31887efb290b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_WidthK_Refine_maskP_nil_left
import Theorems.Thm_WidthK_Refine_maskP_nil_right
import Theorems.Thm_WidthK_Refine_maskP_cons_true
import Theorems.Thm_WidthK_Refine_maskP_cons_false
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution (m : List Bool) (C : PCl) : (maskP m C).Sublist C := by
  induction C generalizing m with
  | nil => rw [maskP_nil_right]
  | cons a C ih =>
    cases m with
    | nil => rw [maskP_nil_left]; exact List.nil_sublist _
    | cons b m =>
      cases b
      · rw [maskP_cons_false]; exact (ih m).cons _
      · rw [maskP_cons_true]; exact (ih m).cons_cons _
end WidthK.Refine
