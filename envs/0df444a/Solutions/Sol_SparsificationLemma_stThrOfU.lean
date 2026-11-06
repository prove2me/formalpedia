-- Prove2me | solution 1 for SparsificationLemma.stThrOfU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:20.858635+00:00
-- url     : https://prove2.me/submissions/fabeab61-8099-47d4-a740-46bc62f6e0c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_UniformInK_Spars_Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Bound
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.mul



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK UniformInK
namespace SparsificationLemma
theorem _root_.solution : StThrOfU := fun _ _ _ _ h1 h => ⟨h.pos, h1, fun i hi hik => h.step i (by omega) hik, h.mul⟩
end SparsificationLemma
