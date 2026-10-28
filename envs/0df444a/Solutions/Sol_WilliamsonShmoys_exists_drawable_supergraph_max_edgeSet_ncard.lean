-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_supergraph_max_edgeSet_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:38:04.130865+00:00
-- url     : https://prove2.me/submissions/58ecb219-4745-4ce1-a01f-63005923bf0a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  let S : Set (SimpleGraph V) := {M | K ≤ M ∧ HasPlanarDrawingOn M}
  have hSfin : S.Finite := Set.finite_univ.subset (by
    intro M hM
    exact Set.mem_univ M)
  obtain ⟨L, hL, hmax⟩ := Set.exists_max_image S (fun M => M.edgeSet.ncard)
    hSfin ⟨K, le_rfl, hDraw⟩
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hMdraw
  exact hmax M ⟨le_trans hL.1 hLM, hMdraw⟩