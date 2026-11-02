-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:47:28.500041+00:00
-- url     : https://prove2.me/submissions/b2a89ef7-a38c-4e2d-8e8e-f6753e3f2ec8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_by_edge_count__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
import Theorems.Thm_WilliamsonShmoys_edge_cardinality_reflects_inclusion__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V),
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v) := by
  classical
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_by_edge_count__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
      H hH
  refine ⟨K, inferInstance, hHK, hK, ?_⟩
  intro L hKL hL u v huv
  have hHL : ∀ ⦃x y : V⦄, H.Adj x y → L.Adj x y := by
    intro x y hxy
    exact hKL (u := x) (v := y) (hHK (u := x) (v := y) hxy)
  have hcount := hmax L hHL hL
  have hreverse :=
    WilliamsonShmoys.edge_cardinality_reflects_inclusion__p2m_04c04e16_b235_4c68_889f_e3b37d35b24b_a1
      (K := K) (L := L) hKL hcount
  exact hreverse u v huv