-- Prove2me | solution 1 for Value.star_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:42:46.290737+00:00
-- url     : https://prove2.me/submissions/b5277dab-02b8-4b24-883e-4125df30dbd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Words

set_option autoImplicit false
section
section
open Value
open Groundwork Finset
namespace Value
theorem _root_.solution {K : ℕ} (Λ : Fin K × Fin K → List Bool) (w w' : Fin K) : star Λ w w' = star Λ w' w := by
  change Λ (min _ _, max _ _) = Λ (min _ _, max _ _)
  rw [min_comm, max_comm]
end Value
