-- Prove2me | solution 1 for VariableBound.Rename.poly_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:26.623498+00:00
-- url     : https://prove2.me/submissions/b1aadf73-b89e-4a65-af72-02c4da0bfcc6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Paper_Rename_Time

set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
namespace VariableBound.Rename
theorem _root_.solution {C C' a : ℕ} (h : C ≤ C') (ha : 1 ≤ a) : C * a ^ C ≤ C' * a ^ C' :=
  Nat.mul_le_mul h (Nat.pow_le_pow_right ha h)
end VariableBound.Rename
