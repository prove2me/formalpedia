-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_local_extension_connected__p2m_92ab9f16_2d15_4356_b6df_90082235199d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:08.118093+00:00
-- url     : https://prove2.me/submissions/757210e6-307c-46e9-b9d1-ad7d2c9c3e62

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_edge_max_extension__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
import Theorems.Thm_WilliamsonShmoys_local_extension_strict_edge_count__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K)
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          P H ∧ G ≤ H ∧
          ∀ x y : V,
            H.Adj x y ↔
              G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    ∃ H : SimpleGraph V,
      P H ∧ H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hH, hKH, hmax⟩ :=
    WilliamsonShmoys.finite_edge_max_extension__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
      P K hK
  refine ⟨H, hH, ?_, hmax K hK le_rfl⟩
  by_contra hdis
  obtain ⟨u, v, huv, H'', hH'', hHH'', hadj⟩ := hstep H hH hdis
  have hlt :=
    WilliamsonShmoys.local_extension_strict_edge_count__p2m_c1868ea9_2f79_4b93_ad6c_bc634ef3355f_a2
      H u v huv H'' hHH'' hadj
  have hbound := hmax H'' hH'' (le_trans hKH hHH'')
  exact (Nat.not_lt_of_ge hbound) hlt
