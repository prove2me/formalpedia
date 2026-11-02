-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_b36e4a06_e569_4990_9a06_8a34b4fc8586_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:42.666965+00:00
-- url     : https://prove2.me/submissions/b9893b47-2216-483c-8045-4221de4892d4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_edge_max__p2m_30ecb5ea_f226_475a_a406_7f8a08cd96a3_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists (fun L : SimpleGraph V => K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall (M : SimpleGraph V), L <= M ->
        WilliamsonShmoys.HasPlanarDrawingOn M -> M <= L)) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_edge_max__p2m_30ecb5ea_f226_475a_a406_7f8a08cd96a3_a2
      K hK
  refine ⟨L, hKL, hL, ?_⟩
  intro M hLM hM
  have hKM : K <= M := le_trans hKL hLM
  have hcard : M.edgeSet.ncard <= L.edgeSet.ncard := hmax M hKM hM
  have hsub : L.edgeSet ⊆ M.edgeSet := SimpleGraph.edgeSet_mono hLM
  have heq : L.edgeSet = M.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  intro a b hab
  have hmem : (Sym2.mk a b) ∈ M.edgeSet := by simpa using hab
  have hmem' : (Sym2.mk a b) ∈ L.edgeSet := by simpa [heq] using hmem
  simpa using hmem'