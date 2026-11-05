-- Prove2me | solution 1 for VariableBound.Search.upsNum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:39.331403+00:00
-- url     : https://prove2.me/submissions/0bf39bd3-062f-499a-a26e-99aacacde9f3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace VariableBound.Search
theorem _root_.solution (m nb β rb tb : ℕ) (x : ℤ) (L : List (List ℕ)) :
    upsNum m nb β rb tb x L = ((4 ^ L.length * 2 ^ tb * (15 * nb) ^ (rb - L.length) : ℕ) : ℤ) * x +
      ((3 ^ L.length * 2 ^ (β - 1) * (15 * nb + 16) ^ (rb - L.length) * loadSum m L : ℕ) : ℤ) := by
  unfold upsNum
  push_cast
  rfl
end VariableBound.Search
