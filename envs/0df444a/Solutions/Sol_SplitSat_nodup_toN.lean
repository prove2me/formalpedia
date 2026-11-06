-- Prove2me | solution 1 for SplitSat.nodup_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:42:23.189386+00:00
-- url     : https://prove2.me/submissions/751ea02b-3f2b-4952-8fff-efd6e446b829

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_SplitSat_Leaf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Eight.Width GraphProblems
namespace SplitSat
theorem _root_.solution {n : ℕ} {φ : Sat3.CNF n} (h : φ.Nodup) : (Decode.toN φ).Nodup := by
  unfold Decode.toN
  refine List.Nodup.map (List.map_injective_iff.2 fun a b e => ?_) h
  exact Prod.ext (Fin.ext (Prod.mk.inj e).1) (Prod.mk.inj e).2
end SplitSat
