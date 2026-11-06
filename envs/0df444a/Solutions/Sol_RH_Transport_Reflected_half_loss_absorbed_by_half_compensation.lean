-- Prove2me | solution 1 for RH.Transport.Reflected.half_loss_absorbed_by_half_compensation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:42.745311+00:00
-- url     : https://prove2.me/submissions/b5769df8-4b4e-4f7b-b4f3-2ced28c3ae57

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_ReflectedExponent

set_option autoImplicit false
open RH RH.Transport RH.Transport.Reflected
noncomputable section
namespace RH.Transport.Reflected
theorem _root_.solution {E d : ℝ}
    (hE : E ≤ 1 / 5) (hd : 0 ≤ d) :
    reflectedLoss E d / 2 - d / 2 ≤ -(3 * d / 8) := by
  have hm : max 0 (5 * E - 1 + d) ≤ d := max_le hd (by linarith)
  unfold reflectedLoss
  linarith
end RH.Transport.Reflected
