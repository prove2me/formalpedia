-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T05:41:21.082216+00:00
-- url     : https://prove2.me/submissions/5db00bc7-4c5b-469a-854a-085d1a528992

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

theorem top_draw2 : WilliamsonShmoys.HasPlanarDrawingOn (⊤ : SimpleGraph (Fin 2)) :=
  draw_le01 2 ⊤ (fun a b hab _ => by
    have := a.isLt; have := b.isLt
    have : a.val < b.val := hab
    omega)

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (G : SimpleGraph V) (dG : DecidableRel G.Adj)
      (hG : HasPlanarDrawingOn G),
      ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
        HasPlanarDrawingOn Q ∧ G ≤ Q ∧
        (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
          HasPlanarDrawingOn K →
          (letI : DecidableRel Q.Adj := dQ
           letI : DecidableRel K.Adj := dK
           Q.edgeFinset.card ≤ K.edgeFinset.card))) := by
  intro h
  obtain ⟨Q, dQ, -, hGQ, hle⟩ := h (V := Fin 2) ⊤ inferInstance top_draw2
  have := hle ⊥ inferInstance (draw_le01 2 ⊥ (fun a b _ hab => absurd hab (by simp)))
  simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_bot,
    Set.ncard_empty] at this
  have hQ01 : Q.Adj 0 1 := hGQ (by simp)
  have h0 : Q.edgeSet.ncard = 0 := by omega
  rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
  have hm : s((0 : Fin 2), 1) ∈ Q.edgeSet := by
    exact hQ01
  rw [h0] at hm
  exact hm
