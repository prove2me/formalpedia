-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_edge_max__p2m_30ecb5ea_f226_475a_a406_7f8a08cd96a3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:27:46.355614+00:00
-- url     : https://prove2.me/submissions/ba20266f-5172-4487-bed7-2bbf9b0b304e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    Exists fun L : SimpleGraph V => K ≤ L ∧
      HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, K ≤ M →
        HasPlanarDrawingOn M →
          M.edgeSet.ncard ≤ L.edgeSet.ncard) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ HasPlanarDrawingOn G
  have hS : S.Nonempty := by
    refine ⟨K, ?_⟩
    simp [S, hK]
  obtain ⟨L, hL, hmax⟩ :=
    Finset.exists_max_image S (fun G => G.edgeSet.ncard) hS
  have hLprops : K ≤ L ∧ HasPlanarDrawingOn L := by
    simpa [S] using hL
  refine ⟨L, hLprops.1, hLprops.2, ?_⟩
  intro M hKM hM
  have hMmem : M ∈ S := by
    simp [S, hKM, hM]
  exact hmax M hMmem