-- Prove2me | solution 1 for Printed.eStarZero_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:44:55.675457+00:00
-- url     : https://prove2.me/submissions/a604d3d9-3d41-4652-8459-d62f02294833

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelCost
import Definitions.Def_Eight_SecPseudocode_Levels
import Mathlib.Tactic
import Definitions.Def_Printed_LevelSentences
import Theorems.Thm_Printed_eStar_le_rho_mul_of
import Theorems.Thm_Eight_eStar_le_rho_mul_of
import Theorems.Thm_Paper_eStar_nonneg
import Theorems.Thm_Printed_eStar_nonneg


set_option autoImplicit false
section
section
open Printed
open Eight Paper QueryMachines
namespace Printed
theorem _root_.solution (hP3 : LevelProposition) : EStarZero := by
  have h1 := eStar_le_rho_mul_of hP3
  have h2 := eStar_nonneg
  have h3 : rho < 1 := by unfold rho; norm_num
  unfold EStarZero
  nlinarith
end Printed
