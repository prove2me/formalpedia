-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_iteration__p2m_7d9aa82d_f2fe_4aa2_b79e_d2d48fb9feb3_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:27:18.518864+00:00
-- url     : https://prove2.me/submissions/e02cb6ed-0cf4-4662-b985-6f0e5316be59

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_bfd9de26_18b5_4f80_88aa_03ffeafbf182_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hstep : ∀ (H : SimpleGraph V), G ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → ¬ H.Connected →
      ∃ (u v : V) (huv : u ≠ v),
        ¬ H.Reachable u v ∧
        ∃ K : SimpleGraph V,
          H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
          ∀ a b, K.Adj a b ↔
            H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ C : SimpleGraph V,
      G ≤ C ∧ C.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn C := by
  obtain ⟨C, hGC, hC, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_bfd9de26_18b5_4f80_88aa_03ffeafbf182_a1 G hG
  by_contra hDisconnected
  have hnotconn : ¬ C.Connected := by
    intro hconn
    exact hDisconnected ⟨C, hGC, hconn, hC⟩
  obtain ⟨u, v, huv, hnotreach, K, hCK, hK, hadj⟩ :=
    hstep C hGC hC hnotconn
  have hKC : K = C := hmax K hCK hK
  have hAdjK : K.Adj u v := by
    exact (hadj u v).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hAdjC : C.Adj u v := by
    rw [← hKC]
    exact hAdjK
  exact hnotreach hAdjC.reachable
