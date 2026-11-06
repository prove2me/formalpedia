-- Prove2me | solution 1 for RH.Transport.Reflected.retained_kernel_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:40.144812+00:00
-- url     : https://prove2.me/submissions/46dc7137-a3db-4b7f-8961-bad592a31c8d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_ReflectedExponent

set_option autoImplicit false
open RH RH.Transport RH.Transport.Reflected
noncomputable section
namespace RH.Transport.Reflected
theorem _root_.solution (Td y : ℝ) :
    Td / 4 ≤ y / 4 + max 0 (Td - y) / 2 := by
  have h0 := le_max_left 0 (Td - y)
  have h1 := le_max_right 0 (Td - y)
  linarith
end RH.Transport.Reflected
