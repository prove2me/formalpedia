-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:27.896873+00:00
-- url     : https://prove2.me/submissions/e14932c1-65c3-4c65-9c95-b59c666873ce

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simple_graph_universe__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
import Theorems.Thm_WilliamsonShmoys_finite_drawable_supergraph_family_maximal__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v) := by
  classical
  let Family : Set (SimpleGraph V) := {K |
    (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K}
  have hFamilyFinite : Family.Finite := by
    apply (WilliamsonShmoys.finite_simple_graph_universe__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1 (V := V)).subset
    intro K hK
    simp only [Set.mem_univ]
  have hFamilyNonempty : Family.Nonempty := by
    refine ⟨H, ?_⟩
    exact ⟨(fun _ _ h => h), hH⟩
  obtain ⟨K, hKFamily, hKMax⟩ :=
    WilliamsonShmoys.finite_drawable_supergraph_family_maximal__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
      Family hFamilyFinite hFamilyNonempty
  refine ⟨K, hKFamily.1, hKFamily.2, ?_⟩
  intro L hKL hLPlanar u v huv
  have hHL : ∀ u v, H.Adj u v → L.Adj u v := by
    intro x y hxy
    exact hKL x y (hKFamily.1 x y hxy)
  have hLFamily : L ∈ Family := ⟨hHL, hLPlanar⟩
  exact hKMax L hLFamily hKL u v huv