-- Prove2me | solution 2 for VariableBound.stParamSpec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:38:18.728059+00:00
-- url     : https://prove2.me/submissions/9c28b0c2-161e-4387-9c3b-e7baaed9400d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
import Theorems.Thm_VariableBound_Spec_isNb_nbD
import Theorems.Thm_VariableBound_Spec_two_le_nbD
import Theorems.Thm_VariableBound_Spec_isRb_rbD
import Theorems.Thm_VariableBound_Spec_isTb_tbD

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
namespace VariableBound
theorem _root_.solution : StParamSpec := ⟨Spec.isNb_nbD, Spec.two_le_nbD, Spec.isRb_rbD, Spec.isTb_tbD⟩
end VariableBound
