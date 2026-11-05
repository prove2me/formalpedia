-- Prove2me | solution 1 for Wrap.Conf.num_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:29:43.676093+00:00
-- url     : https://prove2.me/submissions/026b92c9-1b5c-44bc-8980-9011689cccc9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists

set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
namespace Wrap.Conf
theorem _root_.solution {α : Type} [Finite α] : Function.Injective (num : α → ℕ) :=
  fun _ _ h => (Finite.equivFin α).injective (Fin.val_injective h)
end Wrap.Conf
