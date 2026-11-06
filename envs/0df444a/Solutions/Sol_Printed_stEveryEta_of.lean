-- Prove2me | solution 1 for Printed.stEveryEta_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:29:38.163786+00:00
-- url     : https://prove2.me/submissions/323c08c8-6ef8-48e1-b4c1-5dc1fc82735f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelCost
import Definitions.Def_Eight_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Printed_LevelSentences
import Theorems.Thm_Paper_achievable_of_eStar_lt
import Theorems.Thm_Printed_achievable_of_eStar_lt


set_option autoImplicit false
section
section
open Printed
open Eight Paper QueryMachines
namespace Printed
theorem _root_.solution (h : EStarZero) : StEveryEta := fun η hη K₀ =>
  achievable_of_eStar_lt (by rw [show eStar = 0 from h]; exact hη) K₀
end Printed
