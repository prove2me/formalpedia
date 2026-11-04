-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_formula__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:34:34.0252+00:00
-- url     : https://prove2.me/submissions/012c3202-9aa3-49b7-9811-1f87f1f6b976

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    ∃ f : ℕ,
      (Fintype.card V : ℤ) - (M.edgeFinset.card : ℤ) + (f : ℤ) = 2 := by
  have he : (letI : DecidableRel M.Adj := Classical.decRel M.Adj
      M.edgeFinset) = M.edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_equation_data__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1 M hconn hM
  rw [he] at hf
  refine ⟨f, ?_⟩
  have hf' : (Fintype.card V : ℤ) + (f : ℤ) = (M.edgeFinset.card : ℤ) + 2 := by
    exact_mod_cast hf
  omega