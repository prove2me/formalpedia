-- Prove2me | solution 1 for Wrap.frontEnd_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:11:33.492437+00:00
-- url     : https://prove2.me/submissions/0601072d-81fd-4f93-8d8d-95a181326121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Wrap_slotBits_unary
import Theorems.Thm_Wrap_addFour_polyT
import Theorems.Thm_Wrap_encUnary_polyT
import Theorems.Thm_Groundwork_Decode_dec_polyT


set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode
namespace Wrap
theorem _root_.solution : PolyT frontEnd :=
  encUnary_polyT slotBits_unary (addFour_polyT dec_polyT)
end Wrap
