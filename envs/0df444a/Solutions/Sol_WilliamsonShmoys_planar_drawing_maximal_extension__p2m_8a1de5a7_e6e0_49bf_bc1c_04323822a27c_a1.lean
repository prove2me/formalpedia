-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8a1de5a7_e6e0_49bf_bc1c_04323822a27c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:43:19.362502+00:00
-- url     : https://prove2.me/submissions/aa759b65-bd8b-484d-b660-7fce3e36b065

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_exists_maximal_above__p2m_74778092_2591_4f0d_adff_b80207b549ce_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ u v, L.Adj u v → M.Adj u v) ∧
      ∀ N : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn N →
        (∀ u v, M.Adj u v → N.Adj u v) → N = M := by
  classical
  let P : SimpleGraph V → Prop := WilliamsonShmoys.HasPlanarDrawingOn
  obtain ⟨M, hM, hLM, hmax⟩ :=
    finite_exists_maximal_above__p2m_74778092_2591_4f0d_adff_b80207b549ce_a1 P L hL
  refine ⟨M, hM, ?_, ?_⟩
  · intro u v huv
    exact hLM huv
  · intro N hN hMN
    exact hmax N hN hMN
