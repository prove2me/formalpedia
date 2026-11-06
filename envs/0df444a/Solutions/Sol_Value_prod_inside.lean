-- Prove2me | solution 1 for Value.prod_inside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:31:58.769711+00:00
-- url     : https://prove2.me/submissions/a1b58a15-75f2-49c9-b1e8-3b207f20863a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Sums
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
variable {g K : ℕ}
namespace Value
theorem _root_.solution (χ : Fin g → Fin K) (F : Fin g × Fin g → ℤ) :
    ∏ γ, ∏ p ∈ pairs (Fin g) with χ p.1 = γ ∧ χ p.2 = γ, F p = ∏ p ∈ pairs (Fin g) with χ p.1 = χ p.2, F p := by
  rw [← Finset.prod_fiberwise ((pairs (Fin g)).filter fun p => χ p.1 = χ p.2) (fun p => χ p.1)]
  refine Finset.prod_congr rfl fun γ _ => ?_
  rw [Finset.filter_filter]
  refine Finset.prod_congr (Finset.filter_congr fun p _ => ⟨fun h => ⟨h.1.trans h.2.symm, h.1⟩, fun h => ⟨h.2, h.1 ▸ h.2⟩⟩) fun _ _ => rfl
end Value
