-- Prove2me | solution 1 for WilliamsonShmoys.drawable_extension_maximal__p2m_3c50d639_b449_4a2f_a283_3dfd9e523102_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:16.229017+00:00
-- url     : https://prove2.me/submissions/395cb116-a126-413d-9488-160bf33d5bc1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) [DecidableRel P.Adj] (hP : HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, ∃ hQdec : DecidableRel Q.Adj,
      P ≤ Q ∧ HasPlanarDrawingOn Q ∧
        ∀ (R : SimpleGraph V) (hRdec : DecidableRel R.Adj),
          Q ≤ R → HasPlanarDrawingOn R → R ≤ Q := by
  classical
  let S : Set (SimpleGraph V) := {Q | P ≤ Q ∧ HasPlanarDrawingOn Q}
  have hS_nonempty : S.Nonempty := ⟨P, le_rfl, hP⟩
  have hS_finite : S.Finite := Set.toFinite S
  obtain ⟨Q, hQmax⟩ := hS_finite.exists_maximal hS_nonempty
  have hQS : Q ∈ S := hQmax.1
  have hmax := hQmax.2
  refine ⟨Q, Classical.decRel Q.Adj, hQS.1, hQS.2, ?_⟩
  intro R hRdec hQR hR
  have hRS : R ∈ S := ⟨hQS.1.trans hQR, hR⟩
  exact hmax hRS hQR