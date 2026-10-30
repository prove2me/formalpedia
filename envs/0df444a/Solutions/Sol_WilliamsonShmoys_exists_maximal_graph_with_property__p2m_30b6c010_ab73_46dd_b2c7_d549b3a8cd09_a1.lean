-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_graph_with_property__p2m_30b6c010_ab73_46dd_b2c7_d549b3a8cd09_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:34:36.715858+00:00
-- url     : https://prove2.me/submissions/bdbf332f-5c81-4505-927f-73291e8364bf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ T : SimpleGraph V,
      G.edgeSet ⊆ T.edgeSet ∧
        P T ∧
          ∀ H : SimpleGraph V,
            T.edgeSet ⊆ H.edgeSet → P H → H.edgeSet ⊆ T.edgeSet := by
  classical
  letI : Finite (SimpleGraph V) :=
    Finite.of_injective (fun K : SimpleGraph V => K.edgeSet.toFinset) (by
      intro K L h
      apply SimpleGraph.edgeSet_injective
      ext e
      apply Iff.of_eq
      simpa using congrArg (fun s : Finset (Sym2 V) => e ∈ s) h)
  let candidates : Set (SimpleGraph V) :=
    {K | G.edgeSet ⊆ K.edgeSet ∧ P K}
  have hnonempty : candidates.Nonempty := ⟨G, subset_rfl, hG⟩
  obtain ⟨T, hT, hmax⟩ := (Set.toFinite candidates).exists_maximal hnonempty
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro H hTH hPH
  have hGH : G.edgeSet ⊆ H.edgeSet := hT.1.trans hTH
  have hH : H ∈ candidates := ⟨hGH, hPH⟩
  exact SimpleGraph.edgeSet_subset_edgeSet.mpr (hmax hH
    (SimpleGraph.edgeSet_subset_edgeSet.mp hTH))