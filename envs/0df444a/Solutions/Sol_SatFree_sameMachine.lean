-- Prove2me | solution 1 for SatFree.sameMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:40:57.856513+00:00
-- url     : https://prove2.me/submissions/01b20327-0704-4792-a62e-d9feccae0db4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Order

set_option autoImplicit false
section
section
open SatFree
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : SameMachine := fun k _ _ h n φ hφ => h n φ ⟨fun C hC => (hφ.1 C hC).trans (Nat.le_succ k), hφ.2⟩
end SatFree
