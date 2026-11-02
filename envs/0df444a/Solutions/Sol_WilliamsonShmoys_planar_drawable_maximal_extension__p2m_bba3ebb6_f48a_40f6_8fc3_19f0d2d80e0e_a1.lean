-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension__p2m_bba3ebb6_f48a_40f6_8fc3_19f0d2d80e0e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:07.170762+00:00
-- url     : https://prove2.me/submissions/678bd100-e7c1-4c58-b6b3-e40ef5af66f8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V,
      G.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeFinset ⊆ L.edgeFinset →
        HasPlanarDrawingOn L →
        L.edgeFinset = K.edgeFinset := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  let p : SimpleGraph V → Prop := fun K => G ≤ K ∧ HasPlanarDrawingOn K
  have hp : ∃ K : SimpleGraph V, p K := ⟨G, le_rfl, hG⟩
  obtain ⟨K, hKd, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 hp
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hKedge :
      @SimpleGraph.edgeFinset V K
          (@SimpleGraph.fintypeEdgeSet V K Sym2.instFintype hKd) =
        @SimpleGraph.edgeFinset V K
          (@SimpleGraph.fintypeEdgeSet V K Sym2.instFintype
            (Classical.decRel K.Adj)) := by
    ext e
    simp [SimpleGraph.edgeFinset]
  refine ⟨K, (SimpleGraph.edgeFinset_subset_edgeFinset).2 hmax.1.1,
    hmax.1.2, ?_⟩
  intro L hKL hL
  have hGL : G ≤ L :=
    le_trans hmax.1.1 ((SimpleGraph.edgeFinset_subset_edgeFinset).1 hKL)
  have hLp : p L := ⟨hGL, hL⟩
  have hleCard : L.edgeFinset.card ≤ K.edgeFinset.card := by
    simpa only [hKedge] using hmax.2 hLp
  exact (Finset.eq_of_subset_of_card_le hKL hleCard).symm