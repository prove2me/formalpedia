-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_counts
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:52:20.803989+00:00
-- url     : https://prove2.me/submissions/925115f2-0337-4c33-b023-0f92ae813d8f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181_path_adj (u v : Fin 3) (huv : u < v) (h : (SimpleGraph.pathGraph 3).Adj u v) :
    v.val = u.val + 1 := by
  rw [SimpleGraph.pathGraph_adj] at h
  have : u.val < v.val := huv
  omega

theorem S181_path_draw : WilliamsonShmoys.HasPlanarDrawingOn (SimpleGraph.pathGraph 3) := by
  refine ⟨fun i => (((i : ℕ) : ℝ), (0 : ℝ)),
    fun u v t => ((1 - t) * ((u : ℕ) : ℝ) + t * ((v : ℕ) : ℝ), (0 : ℝ)), ?_, ?_, ?_⟩
  · intro a b h
    simp only [Prod.mk.injEq, Nat.cast_inj, and_true] at h
    exact Fin.ext h
  · intro u v huv hadj
    have hv := S181_path_adj u v huv hadj
    have hv' : ((v : ℕ) : ℝ) = ((u : ℕ) : ℝ) + 1 := by rw [hv]; push_cast; ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (by fun_prop : Continuous fun t : ℝ =>
        ((1 - t) * ((u : ℕ) : ℝ) + t * ((v : ℕ) : ℝ), (0 : ℝ))).continuousOn
    · intro t _ s _ h
      simp only [Prod.mk.injEq, and_true] at h
      rw [hv'] at h
      linarith
    · simp
    · simp
    · intro t ht w h
      simp only [Prod.mk.injEq, and_true] at h
      rw [hv'] at h
      have h1 : ((u : ℕ) : ℝ) < ((w : ℕ) : ℝ) := by linarith [ht.1]
      have h2 : ((w : ℕ) : ℝ) < ((u : ℕ) : ℝ) + 1 := by linarith [ht.2]
      have h1' : (u : ℕ) < (w : ℕ) := by exact_mod_cast h1
      have h2' : (w : ℕ) < (u : ℕ) + 1 := by exact_mod_cast h2
      omega
  · intro u v x y huv hxy hA1 hA2 hne t ht s hs h
    have hv := S181_path_adj u v huv hA1
    have hy := S181_path_adj x y hxy hA2
    have hux : (u : ℕ) ≠ (x : ℕ) := by
      intro e
      apply hne
      have e1 : u = x := Fin.ext e
      have e2 : v = y := Fin.ext (by omega)
      rw [e1, e2]
    have hv3 := v.isLt
    have hy3 := y.isLt
    have hv' : ((v : ℕ) : ℝ) = ((u : ℕ) : ℝ) + 1 := by rw [hv]; push_cast; ring
    have hy' : ((y : ℕ) : ℝ) = ((x : ℕ) : ℝ) + 1 := by rw [hy]; push_cast; ring
    simp only [Prod.mk.injEq, and_true] at h
    rw [hv', hy'] at h
    rcases (by omega : (x : ℕ) = (u : ℕ) + 1 ∨ (u : ℕ) = (x : ℕ) + 1) with e | e
    · have hx : ((x : ℕ) : ℝ) = ((u : ℕ) : ℝ) + 1 := by rw [e]; push_cast; ring
      rw [hx] at h
      have : t = 1 + s := by linarith
      exact ⟨Or.inr (by linarith [ht.2, hs.1]), Or.inl (by linarith [ht.2, hs.1])⟩
    · have hu : ((u : ℕ) : ℝ) = ((x : ℕ) : ℝ) + 1 := by rw [e]; push_cast; ring
      rw [hu] at h
      have : s = 1 + t := by linarith
      exact ⟨Or.inl (by linarith [hs.2, ht.1]), Or.inr (by linarith [hs.2, ht.1])⟩

theorem S181_path_edges : (SimpleGraph.pathGraph 3).edgeSet.ncard = 2 := by
  have : (SimpleGraph.pathGraph 3).edgeSet = {s(0, 1), s(1, 2)} := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj]
      fin_cases a <;> fin_cases b <;> simp
  rw [this, Set.ncard_pair (by simp)]

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V),
    3 ≤ Fintype.card V →
    H.Connected →
    WilliamsonShmoys.HasPlanarDrawingOn H →
    ∃ f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      2 * H.edgeSet.ncard ≤ 3 * f) := by
  intro h
  obtain ⟨f, h1, h2⟩ := h (SimpleGraph.pathGraph 3) (by simp)
    (SimpleGraph.pathGraph_connected 2) S181_path_draw
  rw [S181_path_edges] at h1 h2
  simp only [Fintype.card_fin] at h1
  omega
