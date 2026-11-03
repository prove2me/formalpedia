-- Prove2me | solution 1 for WilliamsonShmoys.maximalPlanarExtensionCardinality__p2m_0ab193fe_0f8a_4383_a58d_9f4c1a7627f8_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:09.580139+00:00
-- url     : https://prove2.me/submissions/b6ebabb7-244d-47ef-bb1b-3dd3f014e8ab

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarTriangulatedExtensionCardinality__p2m_fdcf6722_88f2_45ca_bb18_4e42aed9226b_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N →
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) →
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       N.edgeFinset ⊆ M.edgeFinset))
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel M.Adj := dM
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel M.Adj := dM
  obtain ⟨N, dN, hN, hMN, hNcard⟩ :=
    WilliamsonShmoys.planarTriangulatedExtensionCardinality__p2m_fdcf6722_88f2_45ca_bb18_4e42aed9226b_a2
      M dM hM hn
  letI : DecidableRel N.Adj := dN
  have hNM : N.edgeFinset ⊆ M.edgeFinset := hmax N dN hN hMN
  have hedge : M.edgeFinset = N.edgeFinset := Finset.Subset.antisymm hMN hNM
  rw [hedge]
  exact hNcard
