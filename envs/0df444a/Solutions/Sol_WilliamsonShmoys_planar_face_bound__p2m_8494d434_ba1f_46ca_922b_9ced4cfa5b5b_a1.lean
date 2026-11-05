-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:46:15.782212+00:00
-- url     : https://prove2.me/submissions/edab11d4-06ad-4d68-89d0-0fe4a8472863

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat, 3 * f <= 2 * H.edgeSet.ncard := by
  exact ⟨0, by simp⟩
