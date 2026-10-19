-- Prove2me | solution 1 for PackingBounds.PackingBridge.volume_half_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/2a6cb165-3b99-4c63-a034-1ace1de2206d

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds PackingBounds.PackingBridge
namespace PackingBounds.PackingBridge
theorem _root_.solution {d : ℕ} (hd : 0 < d) :
    volume (ball (0 : CohnElkies.Euclidean d) (1 / 2 : ℝ)) =
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, CohnElkies.sqrt_pi_pow_eq_rpow]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [CohnElkies.unitBallVolume]
  ring
end PackingBounds.PackingBridge
