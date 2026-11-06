-- Prove2me | solution 1 for Printed.eStar_le_rho_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:33:36.692384+00:00
-- url     : https://prove2.me/submissions/222ca517-7c00-4b0f-a71d-01ee67255545

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelCost
import Definitions.Def_Eight_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Printed_LevelSentences
import Theorems.Thm_Printed_eStar_le_of
import Theorems.Thm_Eight_eStar_le_of


set_option autoImplicit false
section
section
open Printed
open Eight Paper QueryMachines
namespace Printed
theorem _root_.solution (hP3 : LevelProposition) : eStar ≤ rho * eStar := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1 : eStar ≤ rho * (eStar + η / 2) + η / 2 := eStar_le_of hP3 (e := eStar + η / 2) (by linarith) (by linarith)
  have h2 : rho * (η / 2) ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right (by unfold rho; norm_num) (by linarith)
  linarith
end Printed
