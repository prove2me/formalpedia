-- Prove2me | solution 1 for WilliamsonShmoys.finite_drawable_supergraph_family_maximal__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:08.85934+00:00
-- url     : https://prove2.me/submissions/d4bf9998-1e57-4723-bbc5-5626e3902daa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Family : Set (SimpleGraph V))
    (hFamilyFinite : Family.Finite)
    (hFamilyNonempty : Family.Nonempty) :
    ∃ K : SimpleGraph V, K ∈ Family ∧
      ∀ L : SimpleGraph V, L ∈ Family →
        (∀ u v, K.Adj u v → L.Adj u v) →
        ∀ u v, L.Adj u v → K.Adj u v := by
  obtain ⟨K, hmax⟩ := hFamilyFinite.exists_maximal hFamilyNonempty
  refine ⟨K, hmax.1, ?_⟩
  intro L hL hKL u v hLuv
  have hLK : L ≤ K := hmax.2 hL hKL
  exact hLK hLuv
