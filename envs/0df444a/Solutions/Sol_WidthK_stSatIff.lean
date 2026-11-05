-- Prove2me | solution 1 for WidthK.stSatIff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:23:09.961251+00:00
-- url     : https://prove2.me/submissions/c90afa5f-f34a-42cf-b079-f2c579cb1d2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_WidthK_SetAlg_sat_iff

set_option autoImplicit false
section
section
open WidthK
namespace WidthK
theorem _root_.solution : StSatIff := fun _ _ _ _ _ v => SetAlg.sat_iff v
end WidthK
