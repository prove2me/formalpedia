-- Prove2me | solution 1 for RecursionToBound.widthOr3F_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:51:56.394819+00:00
-- url     : https://prove2.me/submissions/b987f122-8ff4-45c8-a3a9-feb0f179e2cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Cert_Numbers
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open RecursionToBound
open Finset SparsificationLemma
namespace RecursionToBound
theorem _root_.solution (ψ : Groundwork.Prog.Fml) : widthOr3F ψ = max 3 ((ψ.map List.length).foldr max 0) := by
  rw [widthOr3F, SparsificationLemma.StepSparsify.widthOf, List.foldr_map]
end RecursionToBound
