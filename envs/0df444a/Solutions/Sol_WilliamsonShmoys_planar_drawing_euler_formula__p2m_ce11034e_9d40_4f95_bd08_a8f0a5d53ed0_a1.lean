-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:18:01.3279+00:00
-- url     : https://prove2.me/submissions/dc735827-75a5-4719-9316-29cb8528ba6d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    ∃ f : Nat, Fintype.card V + f = M.edgeFinset.card + 2 := by
  have hedge : (letI : DecidableRel M.Adj := Classical.decRel M.Adj
      M.edgeFinset) = M.edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1 M hconn hM
  refine ⟨f, ?_⟩
  simpa only [hedge] using hf
