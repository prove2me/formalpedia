-- Prove2me | solution 2 for UniformInK.stThrU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:19.160043+00:00
-- url     : https://prove2.me/submissions/c2e13567-10eb-43d6-97a0-cc08950b5694

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Thresholds
import Theorems.Thm_UniformInK_Thresholds_thetaU_pos
import Theorems.Thm_UniformInK_Thresholds_mul_betaSU_le
import Theorems.Thm_UniformInK_Thresholds_step_le
import Theorems.Thm_Groundwork_PB_mul


set_option autoImplicit false
section
section
open UniformInK
open Finset
namespace UniformInK
theorem _root_.solution : StThrU := fun k τ hk hτ =>
  { pos := Thresholds.thetaU_pos (by omega)
    step := fun _ hi hik => Thresholds.step_le hi (by omega)
    mul := Thresholds.mul_betaSU_le τ }
end UniformInK
