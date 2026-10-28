-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_augmentation_from_one_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:17:28.69149+00:00
-- url     : https://prove2.me/submissions/bcaa9e1a-55e6-45f9-9ad3-bd6e790cad1d

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_P_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W)
    (hStep : ∀ G : SimpleGraph V, W ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ G ≠ K ∧ P K) :
    ∃ H : SimpleGraph V,
      W ≤ H ∧ H.Connected ∧ P H ∧ W.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  obtain ⟨H, hWH, hPH, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_P_supergraph W P hP
  have hConnected : H.Connected := by
    by_contra hDisconnected
    obtain ⟨K, hHK, hneq, hPK⟩ := hStep H hWH hPH hDisconnected
    exact hneq (hmax K (le_trans hWH hHK) hHK hPK).symm
  refine ⟨H, hWH, hConnected, hPH, ?_⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hWH)