-- Prove2me | solution 1 for Value.length_blockString
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:44.151583+00:00
-- url     : https://prove2.me/submissions/a5a0f7e1-148a-4291-afee-62ea553bebbd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_mem_tuples
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_pr_of_lt
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]
namespace Value
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) {χ : Fin g → Fin K} {θ : Fin g × Fin g → List Bool} (hθ : θ ∈ blockStrings N χ) {a b : Fin g} (hne : χ a ≠ χ b) :
    (θ (pr a b)).length = Np.cap c a b := by
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  rw [h.given.cap_eq a b hab]
  rcases lt_or_gt_of_ne hab with h' | h'
  · rw [(pr_of_lt h').1]
    exact mem_words.1 (((mem_tuples _ _ _ _).1 hθ (a, b)).1 ⟨h', hne⟩)
  · rw [(pr_of_lt h').2, h.is.c_symm a b]
    exact mem_words.1 (((mem_tuples _ _ _ _).1 hθ (b, a)).1 ⟨h', hne.symm⟩)
end Value
