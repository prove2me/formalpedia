-- Prove2me | solution 1 for WilliamsonShmoys.partition_edge_local_sharp_bound__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:42.310265+00:00
-- url     : https://prove2.me/submissions/e03b76ef-f57e-4be4-b3d0-e45df14fc1e3

import Mathlib
import Theorems.Thm_WilliamsonShmoys_induced_edges_zero_of_card_le_one__p2m_66d9a9d7_c76c_45c0_887d_01a07c3b39fb_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hlocal : ∀ (s : Finset V), (K.induce (↑s : Set V)).Connected → (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _; (K.induce (↑s : Set V)).edgeFinset.card ≤ max 1 (3 * Fintype.card s - 6))) (parts : Finset (Finset V)) (s : Finset V) (hs : s ∈ parts) (hpart : s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _; (K.induce (↑s : Set V)).edgeFinset.card ≤ if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6) := by
  by_cases hc : Fintype.card s ≤ 1
  · have hz := WilliamsonShmoys.induced_edges_zero_of_card_le_one__p2m_66d9a9d7_c76c_45c0_887d_01a07c3b39fb_a2 K s hc
    simp only [if_pos hc]
    rw [hz]
  · by_cases htwo : Fintype.card s = 2
    · have hb := hlocal s hpart.2
      have hm : max 1 (3 * Fintype.card s - 6) = 1 := by
        rw [htwo]
        norm_num
      rw [hm] at hb
      simpa only [if_neg hc, if_pos htwo] using hb
    · have h3 : 3 ≤ Fintype.card s := by omega
      have hb := hlocal s hpart.2
      have hm : max 1 (3 * Fintype.card s - 6) = 3 * Fintype.card s - 6 := by
        apply Nat.max_eq_right
        omega
      rw [hm] at hb
      simpa only [if_neg hc, if_neg htwo] using hb
