-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_connected__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T05:41:19.940844+00:00
-- url     : https://prove2.me/submissions/4ad5e299-c8c9-41a8-abe4-ec410af9bc68

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

/-- Vertices of `Fin n` on the x-axis; the only possible edge is drawn as the segment from 0 to 1. -/
theorem draw_le01 (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : ∀ a b : Fin n, a < b → G.Adj a b → a.val = 0 ∧ b.val = 1) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  refine ⟨fun i => ((i.val : ℝ), 0), fun _ _ t => (t, 0), ?_, ?_, ?_⟩
  · intro a b h
    have := congrArg Prod.fst h
    simp only [Nat.cast_inj] at this
    exact Fin.ext this
  · intro a b hab hadj
    obtain ⟨ha, hb⟩ := hG a b hab hadj
    refine ⟨(continuous_id.prodMk continuous_const).continuousOn, ?_, ?_, ?_, ?_⟩
    · intro x _ y _ h; simpa using congrArg Prod.fst h
    · simp [ha]
    · simp [hb]
    · intro t ht w hw
      have h1 := congrArg Prod.fst hw
      simp only at h1
      have : ((w.val : ℕ) : ℝ) = t := h1.symm
      rcases Nat.lt_or_ge w.val 1 with h | h
      · have : w.val = 0 := by omega
        simp [this] at h1; linarith [ht.1]
      · have : (1 : ℝ) ≤ (w.val : ℝ) := by exact_mod_cast h
        linarith [ht.2]
  · intro a b x y hab hxy h1 h2 hne
    obtain ⟨ha, hb⟩ := hG a b hab h1
    obtain ⟨hx, hy⟩ := hG x y hxy h2
    exact absurd (by rw [Prod.mk.injEq]; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩) hne

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj)
      (hcard : 2 ≤ Fintype.card V) (hQ : HasPlanarDrawingOn Q)
      (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj), HasPlanarDrawingOn K →
        (letI : DecidableRel Q.Adj := dQ; letI : DecidableRel K.Adj := dK;
          Q.edgeFinset.card ≤ K.edgeFinset.card)),
      Q.Connected) := by
  intro h
  have hc := h (V := Fin 2) ⊥ inferInstance (by simp)
    (draw_le01 2 ⊥ (fun a b _ hab => absurd hab (by simp)))
    (fun K dK _ => by
      simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_bot, Set.ncard_empty]
      exact Nat.zero_le _)
  have := hc.preconnected 0 1
  rw [SimpleGraph.reachable_bot] at this
  exact absurd this (by decide)
