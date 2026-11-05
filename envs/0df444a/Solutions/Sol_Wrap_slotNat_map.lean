-- Prove2me | solution 1 for Wrap.slotNat_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:11:17.568541+00:00
-- url     : https://prove2.me/submissions/07a773eb-6149-44d9-af5b-e88d85658d19

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode
namespace Wrap
theorem _root_.solution {n : ℕ} (o : Option (Sat3.Lit n)) : slotNat (o.map fun l => (l.1.val, l.2)) = Sat3.slot o := by
  cases o <;> rfl
end Wrap
