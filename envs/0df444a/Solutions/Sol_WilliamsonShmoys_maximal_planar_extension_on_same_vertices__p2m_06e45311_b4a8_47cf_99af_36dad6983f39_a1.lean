-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_on_same_vertices__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- status  : ACCEPTED   (disprove)
-- author  : @もち
-- created : 2026-11-24T05:41:21.546874+00:00
-- url     : https://prove2.me/submissions/07943f13-b92a-437e-a733-5e9c11ee6cc4

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
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
      (hcard : 3 ≤ Fintype.card V),
      letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
        fun G => Classical.decRel G.Adj
      ∃ H : SimpleGraph V,
        HasPlanarDrawingOn H ∧
        (∀ {u v : V}, K.Adj u v → H.Adj u v) ∧
        (∀ H' : SimpleGraph V,
          (∀ {u v : V}, H'.Adj u v → H.Adj u v) →
          HasPlanarDrawingOn H' → H' = H) ∧
        K.edgeFinset.card ≤ H.edgeFinset.card) := by
  intro h
  let K : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet {s(0, 1)}
  have hKd : HasPlanarDrawingOn K := draw_le01 3 K (fun a b hab hadj => by
    simp only [K, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hadj
    have : a.val < b.val := hab
    rcases hadj.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · simp at this)
  obtain ⟨H, -, hKH, hmin, -⟩ := h (V := Fin 3) K hKd (by simp)
  have hbot := hmin ⊥ (fun hb => absurd hb (by simp))
    (draw_le01 3 ⊥ (fun a b _ hab => absurd hab (by simp)))
  have h01 : H.Adj 0 1 := hKH (by simp [K])
  rw [← hbot] at h01
  simp at h01
