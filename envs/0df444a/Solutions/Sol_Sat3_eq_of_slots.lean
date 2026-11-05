-- Prove2me | solution 1 for Sat3.eq_of_slots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:45:15.681375+00:00
-- url     : https://prove2.me/submissions/53c1fd3c-8138-4f20-87cc-46175e153ae9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Math_Formula

set_option autoImplicit false
section
open Sat3
namespace Sat3
theorem _root_.solution {n : ℕ} {C D : List (Lit n)} (hC : C.length ≤ 3) (hD : D.length ≤ 3)
    (h : ∀ j < 3, C[j]? = D[j]?) : C = D :=
  List.ext_getElem? fun j => by
    by_cases hj : j < 3
    · exact h j hj
    · rw [List.getElem?_eq_none (by grind), List.getElem?_eq_none (by grind)]
end Sat3
