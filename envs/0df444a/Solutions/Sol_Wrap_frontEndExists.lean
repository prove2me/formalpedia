-- Prove2me | solution 1 for Wrap.frontEndExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:14:01.808253+00:00
-- url     : https://prove2.me/submissions/63caf2cc-aa67-4386-9677-9af3c275b248

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Wrap_frontEnd_enc
import Theorems.Thm_Wrap_frontEnd_polyT

set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode
namespace Wrap
theorem _root_.solution : FrontEndExists :=
  ⟨frontEnd, frontEnd_polyT, fun _ _ hφ => frontEnd_enc hφ.1⟩
end Wrap
