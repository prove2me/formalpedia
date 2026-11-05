-- Prove2me | solution 1 for WidthK.stHeavyEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:23:21.574363+00:00
-- url     : https://prove2.me/submissions/d040b2a9-c92c-43c8-8a70-7738d2950c3d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_WidthK_SetAlg_heavy_eq

set_option autoImplicit false
section
section
open WidthK
namespace WidthK
theorem _root_.solution : StHeavyEq := fun _ _ _ _ _ _ hF h => SetAlg.heavy_eq hF h
end WidthK
