-- Prove2me | solution 1 for WardropTraffic.Signal.partials_at_corner
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:26:43.053878+00:00
-- url     : https://prove2.me/submissions/067ab73d-7e7e-4ffe-9f06-05fe182a5cdb

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting

open WardropTraffic.Signal

theorem solution (lam mu xi eta : ℝ) (hsum : 1 < xi + eta) :
    HasDerivAt (fun x => delayT lam mu x eta)
        ((lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta)) / (xi + eta - 1) ^ 2) xi ∧
      HasDerivAt (fun y => delayT lam mu xi y)
        ((mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi)) / (xi + eta - 1) ^ 2) eta := by
  have hn : xi + eta - 1 ≠ 0 := by linarith
  constructor
  · convert (((hasDerivAt_id xi).pow 2).const_mul lam |>.add_const (mu * eta ^ 2)).div
      (((hasDerivAt_id xi).add_const eta).sub_const 1) hn using 1 <;>
      first | rfl | (simp [delayT, Pi.div_def, Pi.pow_apply]; ring) |
        (ext x; simp [delayT, Pi.div_def, Pi.pow_apply]; ring)
  · convert ((hasDerivAt_const eta (lam * xi ^ 2)).add
      (((hasDerivAt_id eta).pow 2).const_mul mu)).div
      (((hasDerivAt_id eta).const_add xi).sub_const 1) hn using 1 <;>
      first | rfl | (simp [delayT, Pi.div_def, Pi.pow_apply]; ring) |
        (ext y; simp [delayT, Pi.div_def, Pi.pow_apply]; ring)

#print axioms solution
