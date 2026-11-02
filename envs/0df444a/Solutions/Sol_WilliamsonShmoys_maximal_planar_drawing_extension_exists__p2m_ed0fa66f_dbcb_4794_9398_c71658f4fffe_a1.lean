-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_extension_exists__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:15:03.685207+00:00
-- url     : https://prove2.me/submissions/014f36a3-6711-4732-af33-3f3b57429ebb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      G <= N /\ HasPlanarDrawingOn N /\
        (forall M : SimpleGraph V, N <= M -> HasPlanarDrawingOn M -> M <= N) := by
  classical
  let S : Set (SimpleGraph V) := {N | G <= N /\ HasPlanarDrawingOn N}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    exact ⟨G, le_rfl, hG⟩
  obtain ⟨N, hN⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨N, hN.1.1, hN.1.2, ?_⟩
  intro M hNM hM
  have hMS : M ∈ S := ⟨le_trans hN.1.1 hNM, hM⟩
  exact hN.2 hMS hNM