-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:40.737052+00:00
-- url     : https://prove2.me/submissions/a6f912f6-c6a5-4629-a003-4f33d1b4ac50

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V), ∃ (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
        ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
          HasPlanarDrawingOn K → H ≤ K → K ≤ H := by
  classical
  let S : Set (SimpleGraph V) := {H | HasPlanarDrawingOn H ∧ G ≤ H}
  have hSfinite : S.Finite := Set.finite_univ.subset (by
    intro H hH
    exact Set.mem_univ H)
  have hSnonempty : S.Nonempty := ⟨G, hG, le_rfl⟩
  obtain ⟨H, hmax⟩ := hSfinite.exists_maximal hSnonempty
  change H ∈ S ∧ ∀ ⦃K⦄, K ∈ S → H ≤ K → K ≤ H at hmax
  rcases hmax with ⟨hHmem, hmax⟩
  rcases hHmem with ⟨hHplanar, hGH⟩
  refine ⟨H, inferInstance, hHplanar, hGH, ?_⟩
  intro K dK hKplanar hHK
  exact hmax ⟨hKplanar, le_trans hGH hHK⟩ hHK