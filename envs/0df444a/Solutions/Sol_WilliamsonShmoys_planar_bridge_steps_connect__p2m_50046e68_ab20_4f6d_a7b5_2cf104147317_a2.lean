-- Prove2me | solution 1 for WilliamsonShmoys.planar_bridge_steps_connect__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:56:23.530032+00:00
-- url     : https://prove2.me/submissions/010c5469-9899-4874-b828-6393e0309c15

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_bounded_finite_ascent__p2m_6759599f_0df8_4b6f_bc89_5739bb0b46dc_a3
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hstep : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ u v : V, ∃ H : SimpleGraph V,
        ¬ G.Adj u v ∧ G ≤ H ∧ H.Adj u v ∧ HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  classical
  let rank : SimpleGraph V → ℕ := fun G =>
    (Finset.univ.filter fun p : V × V => G.Adj p.1 p.2).card
  have hbound (G : SimpleGraph V) : rank G ≤ Fintype.card (V × V) := by
    dsimp [rank]
    calc
      _ ≤ (Finset.univ : Finset (V × V)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card (V × V) := Finset.card_univ
  have hrank {G H : SimpleGraph V} (hGH : G ≤ H) {u v : V}
      (hnew : ¬ G.Adj u v) (hHv : H.Adj u v) : rank G < rank H := by
    dsimp [rank]
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hGH hp
    · intro heq
      have hpH : (u, v) ∈ Finset.univ.filter fun p : V × V => H.Adj p.1 p.2 := by
        simp [hHv]
      rw [← heq] at hpH
      have hpG : G.Adj u v := (Finset.mem_filter.mp hpH).2
      exact hnew hpG
  have hmeasure
      (G : SimpleGraph V) (hG : HasPlanarDrawingOn G ∧ K ≤ G)
      (hnot : ¬ G.Connected) :
      ∃ H : SimpleGraph V,
        (HasPlanarDrawingOn H ∧ K ≤ H) ∧
        rank G < rank H ∧ rank H ≤ Fintype.card (V × V) := by
    rcases hG with ⟨hplanar, hKG⟩
    obtain ⟨u, v, H, hnew, hGH, hHv, hH⟩ := hstep G hplanar hnot
    exact ⟨H, ⟨hH, le_trans hKG hGH⟩, hrank hGH hnew hHv, hbound H⟩
  obtain ⟨H, ⟨hH, hKH⟩, hconn⟩ :=
    WilliamsonShmoys.bounded_finite_ascent__p2m_6759599f_0df8_4b6f_bc89_5739bb0b46dc_a3
      (fun G : SimpleGraph V => HasPlanarDrawingOn G ∧ K ≤ G)
      (fun G : SimpleGraph V => G.Connected) rank (Fintype.card (V × V)) K
      ⟨hK, le_rfl⟩ (hbound K) hmeasure
  exact ⟨H, hKH, hconn, hH⟩