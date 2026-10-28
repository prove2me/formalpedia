-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_drawable_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:21:56.191056+00:00
-- url     : https://prove2.me/submissions/fdbba909-345d-4ecd-996a-b456ab48be30

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open scoped Classical

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  classical
  let p : SimpleGraph V → Prop := fun G => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hp : ∃ G : SimpleGraph V, p G := ⟨K, le_rfl, hK⟩
  obtain ⟨L, hDec, hLmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel L.Adj := hDec
  refine ⟨L, hLmax.1.1, hLmax.1.2, ?_⟩
  intro M hLM hM
  have hpM : p M := ⟨hLmax.1.1.trans hLM, hM⟩
  have hEq : L = M :=
    (SimpleGraph.IsExtremal.le_iff_eq hLmax hpM).1 hLM
  rw [← hEq]