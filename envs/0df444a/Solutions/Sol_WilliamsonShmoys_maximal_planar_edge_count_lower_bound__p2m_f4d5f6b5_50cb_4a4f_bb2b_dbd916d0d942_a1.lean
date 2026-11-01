-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:02.224859+00:00
-- url     : https://prove2.me/submissions/5722cdbe-01b1-43db-85b3-4de9a3059fef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_58b7864f_b594_4fea_9b4c_5ab78bff59aa_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      M.edgeFinset ⊆ N.edgeFinset -> N.edgeFinset ⊆ M.edgeFinset)
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= M.edgeFinset.card := by
  classical
  obtain ⟨N, dN, hN, hMN, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_58b7864f_b594_4fea_9b4c_5ab78bff59aa_a1
      M dM hM hcard
  have hNM : N.edgeFinset ⊆ M.edgeFinset := hmax N dN hN hMN
  have hEq : N.edgeFinset = M.edgeFinset := Finset.Subset.antisymm hNM hMN
  calc
    3 * Fintype.card V - 6 = N.edgeFinset.card := hcount.symm
    _ = M.edgeFinset.card := congrArg Finset.card hEq
    _ <= M.edgeFinset.card := le_rfl