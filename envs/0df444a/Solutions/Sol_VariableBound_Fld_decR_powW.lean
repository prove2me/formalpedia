-- Prove2me | solution 1 for VariableBound.Fld.decR_powW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:11:59.176147+00:00
-- url     : https://prove2.me/submissions/3d87bf18-69a1-4c5e-8605-36b308a33619

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Field_Ring
import Theorems.Thm_VariableBound_Fld_powW_succ
import Theorems.Thm_VariableBound_Fld_length_powW
import Theorems.Thm_VariableBound_Fld_decR_oneW
import Theorems.Thm_VariableBound_Fld_decR_mulW

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
variable {R : Type} [CommRing R]
namespace VariableBound.Fld
theorem _root_.solution (h2 : (2 : R) = 0) {r : R} {g : List Bool} (hr : r ^ g.length = decR r g) (hg : 1 ≤ g.length) (u : List Bool) (e : ℕ) :
    decR r (powW g u e) = decR r u ^ e := by
  induction e with
  | zero =>
    have e0 : powW g u 0 = oneW g := rfl
    rw [e0, decR_oneW, pow_zero]
  | succ e ih => rw [powW_succ, decR_mulW h2 hr (length_powW hg u e), ih, pow_succ]
end VariableBound.Fld
