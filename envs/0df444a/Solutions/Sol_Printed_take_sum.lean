-- Prove2me | solution 1 for Printed.take_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:54:08.05325+00:00
-- url     : https://prove2.me/submissions/35ee74ca-bbd1-48f1-9e29-7cdb4377bd8a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
import Theorems.Thm_Printed_sum_lengths
import Theorems.Thm_Printed_map_length_ofFn
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}
namespace Printed
theorem _root_.solution (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) (i : ℕ) (hi : i ≤ K) :
    (((List.ofFn θ).map List.length).take i).sum = (if w.val < i then i - 1 else i) * lam := by
  rw [map_length_ofFn w θ h hw, ← List.map_take, List.take_range, min_eq_left hi, sum_lengths]
end Printed
