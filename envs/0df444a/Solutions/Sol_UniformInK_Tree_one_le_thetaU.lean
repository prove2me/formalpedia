-- Prove2me | solution 1 for UniformInK.Tree.one_le_thetaU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:12.124137+00:00
-- url     : https://prove2.me/submissions/7c74ffb8-d529-447f-98c6-143c49a4d71f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Tree_Tree
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate WidthK.Prog
open UniformInK.Tree
namespace UniformInK.Tree
theorem _root_.solution {τ : ℕ} (hτ : 1 ≤ τ) : ∀ i, 1 ≤ thetaU τ i
  | 0 => le_refl 1
  | i + 1 => Nat.mul_pos (by norm_num) (Nat.pow_pos hτ)
end UniformInK.Tree
