-- Prove2me | solution 1 for WidthK.Refine.not_heart_of_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:27:05.822573+00:00
-- url     : https://prove2.me/submissions/da1d1d68-74f8-471d-b665-aa5ffa41aac3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_WidthK_Refine_mem_pairsK
import Theorems.Thm_WidthK_Refine_tryP_none
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {j : ℕ} {H : Finset PLit} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (hj : j ≤ k) (h : (j, H.card) ∈ pairsK k → tryP θ k s (j, H.card) = none) : ¬ Heart θ (toFin s) j H := by
  intro hh
  have hm : (j, H.card) ∈ pairsK k := mem_pairsK.2 ⟨Finset.card_pos.2 hh.1, hh.2.1, hj⟩
  exact tryP_none hθ hs hm (h hm) H rfl hh
end WidthK.Refine
