-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_maximal_extension__p2m_dfeab8e7_c65a_497d_a20d_7cce49bd8d27_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:46.972541+00:00
-- url     : https://prove2.me/submissions/bce92bc7-9873-4cd7-933b-04daa7fd5571

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hP : P H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let S : Finset (SimpleGraph V) := Finset.univ.filter fun G => H ≤ G ∧ P G
  have hHmem : H ∈ S := by
    simp [S, hP]
  have hS : S.Nonempty := ⟨H, hHmem⟩
  obtain ⟨K, hKmem, hKmax⟩ :=
    S.exists_max_image (fun G => G.edgeSet.ncard) hS
  have hHK : H ≤ K := (Finset.mem_filter.mp hKmem).2.1
  have hPK : P K := (Finset.mem_filter.mp hKmem).2.2
  refine ⟨K, hHK, hPK, ?_, ?_⟩
  · exact hKmax H hHmem
  · intro L hKL hPL
    apply hKmax L
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ L, le_trans hHK hKL, hPL⟩