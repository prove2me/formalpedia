-- Prove2me | solution 1 for Printed.length_flatten_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:02:08.725369+00:00
-- url     : https://prove2.me/submissions/34d8c619-e709-4c56-933d-4dc7926dfa19

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
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}
namespace Printed
theorem _root_.solution (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) :
    (List.ofFn θ).flatten.length = (K - 1) * lam := by
  rw [List.length_flatten, map_length_ofFn w θ h hw, sum_lengths, if_pos w.2]
end Printed
