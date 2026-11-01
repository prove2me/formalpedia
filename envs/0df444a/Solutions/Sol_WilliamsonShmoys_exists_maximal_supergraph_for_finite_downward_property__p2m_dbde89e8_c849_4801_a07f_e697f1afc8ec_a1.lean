-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_finite_downward_property__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:28.855148+00:00
-- url     : https://prove2.me/submissions/c2768809-17ac-4e5c-aa8f-8b5a9ed372b4

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P H)
    (hdown : ∀ ⦃G G' : SimpleGraph V⦄, G ≤ G' → P G' → P G) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  classical
  let S : Set (SimpleGraph V) := {G | H ≤ G ∧ P G}
  have hS : S.Finite := Set.toFinite S
  have hH : H ∈ S := ⟨le_rfl, hP⟩
  obtain ⟨K, hHK, hKmax⟩ := hS.exists_le_maximal hH
  refine ⟨K, hHK, hKmax.1.2, ?_⟩
  intro L hKL hPL
  have hHL : H ≤ L := hHK.trans hKL
  exact hKmax.2 ⟨hHL, hPL⟩ hKL