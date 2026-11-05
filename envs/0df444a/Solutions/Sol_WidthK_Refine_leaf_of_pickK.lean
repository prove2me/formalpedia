-- Prove2me | solution 1 for WidthK.Refine.leaf_of_pickK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:28:11.574+00:00
-- url     : https://prove2.me/submissions/af3546a6-5e0a-4395-a94a-8f1e680dbfe0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_WidthK_Refine_pickK_none
import Theorems.Thm_WidthK_Refine_not_heart_of_none
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {θ : ℕ → ℕ} {k : ℕ} {s : PFml} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (h : pickK θ k s = none) : Leaf θ k (toFin s) :=
  fun _ hj _ => not_heart_of_none hθ hs hj fun hm => pickK_none h _ hm
end WidthK.Refine
