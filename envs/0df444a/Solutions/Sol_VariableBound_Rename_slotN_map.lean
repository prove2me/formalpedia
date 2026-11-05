-- Prove2me | solution 1 for VariableBound.Rename.slotN_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:15.998262+00:00
-- url     : https://prove2.me/submissions/f0bba847-9f8f-4c49-bf47-351283795907

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Code
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
namespace VariableBound.Rename
theorem _root_.solution {n : ℕ} (o : Option (Sat3.Lit n)) : slotN (o.map fun l => (l.1.val, l.2)) = Sat3.slot o := by
  cases o <;> rfl
end VariableBound.Rename
