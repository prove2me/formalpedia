-- Prove2me | solution 1 for SingleBitPieces.SecPseudocode_Levels.levelK_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:31:02.079616+00:00
-- url     : https://prove2.me/submissions/a775fd99-2d2c-4543-8a25-59c4152606a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecPseudocode_Algorithm
import Definitions.Def_KSatStatement
import Mathlib.Tactic
import Definitions.Def_SingleBitPieces_SecPseudocode_Levels
import Theorems.Thm_Paper_levelK_ge


set_option autoImplicit false
section
section
open SingleBitPieces
open Paper Groundwork
open SingleBitPieces.SecPseudocode_Levels
namespace SingleBitPieces.SecPseudocode_Levels
theorem _root_.solution (ℓ : ℕ) : (0 : ℝ) < levelK ℓ := by
  exact_mod_cast lt_of_lt_of_le (by norm_num) (levelK_ge ℓ)
end SingleBitPieces.SecPseudocode_Levels
