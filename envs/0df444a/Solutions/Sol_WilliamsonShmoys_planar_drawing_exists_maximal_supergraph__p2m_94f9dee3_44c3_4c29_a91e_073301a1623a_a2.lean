-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exists_maximal_supergraph__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:37.580486+00:00
-- url     : https://prove2.me/submissions/39e6e551-ba51-4509-9761-405b892b3524
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_card_max_drawable_supergraph__p2m_e7afab76_b36c_483c_9361_7e3fa4f8788a_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        K.edgeFinset ⊆ L.edgeFinset →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeFinset ⊆ K.edgeFinset) := by
  classical
  obtain ⟨K, hKDec, hHK, hKrest⟩ :=
    WilliamsonShmoys.exists_card_max_drawable_supergraph__p2m_e7afab76_b36c_483c_9361_7e3fa4f8788a_a1
      H hH
  letI : DecidableRel K.Adj := hKDec
  rcases hKrest with ⟨hKplanar, hKmax⟩
  refine ⟨K, inferInstance, hHK, hKplanar, ?_⟩
  intro L _ hKL hLplanar
  by_contra hback
  have hstrict : K.edgeFinset ⊂ L.edgeFinset :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hKL, by
      intro heq
      have hLK : L.edgeFinset ⊆ K.edgeFinset := by
        simpa [heq] using hKL
      exact hback hLK⟩
  have hcard := Finset.card_lt_card hstrict
  have hHL : H.edgeFinset ⊆ L.edgeFinset := hHK.trans hKL
  have hmax := hKmax L hHL hLplanar
  omega
