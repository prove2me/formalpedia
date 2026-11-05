-- Prove2me | solution 1 for WidthK.stLightEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:19:45.023512+00:00
-- url     : https://prove2.me/submissions/cbd8293e-22b6-480f-a0e5-b52a96c8118c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_WidthK_SetAlg_light_eq

set_option autoImplicit false
section
section
open WidthK
namespace WidthK
theorem _root_.solution : StLightEq := fun _ _ _ _ _ _ hθ hF h => SetAlg.light_eq hθ hF h
end WidthK
