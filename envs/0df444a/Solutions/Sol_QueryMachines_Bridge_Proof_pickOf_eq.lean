-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.pickOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:09.10345+00:00
-- url     : https://prove2.me/submissions/90c7d143-a7a4-45b4-8221-71d01dcf2278

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_CountedToPadded_Pick
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.PolyT PaddedDescent.F Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (kf : U × U → Option U) (K₀ : ℕ) (b : U) : pickOf kf K₀ b = (((List.range (b.length + 1)).filterMap (cand kf b)).getLast?).getD ([], ([], unary K₀)) := rfl
end QueryMachines.Bridge.Proof
