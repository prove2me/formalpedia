-- Prove2me | solution 1 for Sat3.Is3CNF.length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:46:15.509556+00:00
-- url     : https://prove2.me/submissions/bfa41a3f-23d3-4a6b-81fc-7ff70b3bc201

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Math_Formula
import Theorems.Thm_Sat3_eq_of_slots

set_option autoImplicit false
section
open Sat3
namespace Sat3
namespace Is3CNF
theorem _root_.solution {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : φ.length ≤ (2 * n + 1) ^ 3 := by
  have := (h.2.map_on (f := fun C (j : Fin 3) => C[(j : ℕ)]?) fun C hC D hD e =>
    eq_of_slots (h.1 C hC) (h.1 D hD) fun j hj => congrFun e ⟨j, hj⟩).length_le_card
  simpa [mul_comm] using this
end Is3CNF
end Sat3
