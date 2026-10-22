-- Prove2me | solution 1 for SDDiP.Envelope.conv_binary_eq_cube
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:20:25.723186+00:00
-- url     : https://prove2.me/submissions/e1cace34-629a-425b-8d2b-29bc2e941004

import Mathlib
import Definitions.Def_SDDiP_Envelope_ConvexLowerEnvelope

set_option autoImplicit false
open SDDiP.Envelope

theorem solution (n : ℕ) : convexHull ℝ (binaryPoints n) = cube n := by
  have h1 : binaryPoints n = Set.pi Set.univ (fun _ : Fin n => ({0, 1} : Set ℝ)) := by
    ext x
    simp [binaryPoints, Set.mem_pi]
  rw [h1, convexHull_pi]
  ext x
  simp [cube, Set.mem_pi, convexHull_pair, segment_eq_Icc (zero_le_one : (0:ℝ) ≤ 1), Pi.le_def]
