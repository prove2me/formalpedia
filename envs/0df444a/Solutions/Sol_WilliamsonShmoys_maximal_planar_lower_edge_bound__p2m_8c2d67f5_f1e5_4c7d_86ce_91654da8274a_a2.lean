-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:54:29.461645+00:00
-- url     : https://prove2.me/submissions/e8e31db9-2421-4bcc-a6ef-1b9bc9e7961f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_augmentation_below_planar_bound__p2m_6aea0192_1a29_46e3_846e_b5510acd39b3_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset = L.edgeFinset) :
    3 * Fintype.card V - 6 <= L.edgeFinset.card := by
  by_contra hnot
  have hsmall : L.edgeFinset.card < 3 * Fintype.card V - 6 :=
    Nat.lt_of_not_ge hnot
  obtain ⟨M, dM, hM, hsub, hne⟩ :=
    WilliamsonShmoys.edge_augmentation_below_planar_bound__p2m_6aea0192_1a29_46e3_846e_b5510acd39b3_a1
      L dL hL hn hsmall
  exact hne (hmax M dM hM hsub).symm