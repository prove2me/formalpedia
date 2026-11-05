-- Prove2me | solution 1 for WidthK.Refine.pickK_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:24:05.378523+00:00
-- url     : https://prove2.me/submissions/e9a30126-9d57-4852-aa3e-6cd02d3a6139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_P2M_WidthK_Refine_head__filterMap_eq_none_b77b38f5a50f
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {θ : ℕ → ℕ} {k : ℕ} {s : PFml} (h : pickK θ k s = none) : ∀ x ∈ pairsK k, tryP θ k s x = none :=
  head?_filterMap_eq_none h
end WidthK.Refine
