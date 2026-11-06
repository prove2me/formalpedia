-- Prove2me | solution 1 for Printed.stAnswerEachQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:08:50.826325+00:00
-- url     : https://prove2.me/submissions/f8f2c48d-f087-4696-aade-247ddba4f51a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable
import Theorems.Thm_Printed_tables_eq_some
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_const
import Theorems.Thm_QueryMachines_stPlug
import Theorems.Thm_QueryMachines_stQueriesLe
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution : StAnswerEachQuery := fun M Cc K e h lam B W hl hB hW => by
  obtain ⟨T, hw, hT⟩ := h lam B W hl hB hW
  obtain ⟨own, L, hr, hle⟩ := QueryMachines.stQueriesLe _ _ _ _ M _ _ _ _ _ hw
  refine ⟨⟨own, L, hr, le_trans (by exact_mod_cast (by omega : L.length ≤ T)) hT⟩, fun C _ R c t S ht hR => ?_⟩
  have hp := QueryMachines.stPlug _ _ C _ _ M R (tables K lam W) c _ own _ S L _ (fun _ => t) hr fun x _ v hv => by
    obtain ⟨h1, h2, rfl⟩ := tables_eq_some hv
    exact hR x.1 h1 x.2 h2
  refine ⟨_, hp, ?_⟩
  rw [QueryMachine.sum_map_const]
  have h1 : own + L.length * (t + 2) ≤ T * (3 * t) :=
    calc own + L.length * (t + 2) ≤ own * (3 * t) + L.length * (3 * t) := Nat.add_le_add (Nat.le_mul_of_pos_right _ (by omega)) (Nat.mul_le_mul_left _ (by omega))
      _ = (own + L.length) * (3 * t) := by ring
      _ ≤ T * (3 * t) := Nat.mul_le_mul_right _ hle
  calc ((own + L.length * (t + 2) : ℕ) : ℝ) ≤ ((T * (3 * t) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 3 * (T : ℝ) * t := by push_cast; ring
    _ ≤ 3 * (Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc) * t := by gcongr
end Printed
