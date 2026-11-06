-- Prove2me | solution 1 for RH.Transport.Endpoint.countDenominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:25:11.138408+00:00
-- url     : https://prove2.me/submissions/070633da-cdc1-4197-a7db-1ad20119c1ca

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section
namespace RH.Transport.Endpoint
theorem _root_.solution {δ x : ℝ}
    (hdlo : (1 / 50 : ℝ) ≤ δ) (hdhi : δ ≤ 3 / 4)
    (_hxlo : 0 ≤ x) (hxhi : x ≤ 1 / 2) : 0 < countDenominator δ x := by
  have hd : 0 < δ := by linarith
  have ha : 0 < (5 / 6 : ℝ) - δ := by linarith
  have hD : 0 < (3 : ℝ) - 17 * x / 9 := by linarith
  have hP : 0 < ((2 : ℝ) - 8 * x / 9) * (1 - x) :=
    mul_pos (by linarith) (by linarith)
  exact add_pos (mul_pos ha hD) (mul_pos hd hP)
end RH.Transport.Endpoint
