-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_19232441_686a_4272_ba92_bbecb802c741_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:24:43.788876+00:00
-- url     : https://prove2.me/submissions/d368e7a8-e2b3-4f16-92aa-92104f2eca70

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_type_finite__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_set__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ L : SimpleGraph V, H ≤ L → L ≠ H → ¬ P L := by
  classical
  let S : Set (SimpleGraph V) := {H | K ≤ H ∧ P H}
  have hS : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_mem_set__p2m_cef71128_5f51_4c32_b585_a6c07850dc7b_a1 S hS
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro L hHL hne hPL
  have hL : L ∈ S := ⟨le_trans hH.1 hHL, hPL⟩
  exact hne (hmax L hHL hL)