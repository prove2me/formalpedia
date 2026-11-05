-- Prove2me | solution 1 for WidthK.Refine.rule_of_pickK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:28:07.353059+00:00
-- url     : https://prove2.me/submissions/773a9d65-2ac6-4ca3-8019-17d923323241

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_WidthK_Refine_mem_pairsK
import Theorems.Thm_WidthK_Refine_pickK_some
import Theorems.Thm_WidthK_Refine_tryP_some
import Theorems.Thm_WidthK_Refine_not_heart_of_none
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.Refine
theorem _root_.solution {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {HP : PCl × PFml} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (h : pickK θ k s = some HP) :
    ∃ j, HP.1.Nodup ∧ Rule θ k (toFin s) j HP.1.toFinset ∧ HP.2 = (overP s j HP.1).map (minusP HP.1) := by
  obtain ⟨jh, hjh, h1, h2⟩ := pickK_some h
  obtain ⟨hnd, hcard, hheart, hP⟩ := tryP_some hs hjh h1
  obtain ⟨-, -, hk⟩ := mem_pairsK.1 hjh
  refine ⟨jh.1, hnd, ⟨hk, hheart, ?_, ?_⟩, hP⟩
  · intro j' hj' H'
    exact not_heart_of_none hθ hs (by omega) fun hm => h2 _ hm (Or.inl hj')
  · intro H' hH'
    exact not_heart_of_none hθ hs hk fun hm => h2 _ hm (Or.inr ⟨rfl, by rw [← hcard]; exact hH'⟩)
end WidthK.Refine
