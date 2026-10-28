-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_components
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:49:16.176986+00:00
-- url     : https://prove2.me/submissions/0c9414eb-2cc9-4ab8-a7ba-de0d37671281

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem path3_adj {u v : Fin 3} (h : u < v) (hadj : (SimpleGraph.pathGraph 3).Adj u v) :
    v.val = u.val + 1 := by
  rw [SimpleGraph.pathGraph_adj] at hadj
  have : u.val < v.val := h
  omega

theorem path3_drawing : HasPlanarDrawingOn (SimpleGraph.pathGraph 3) := by
  refine ⟨fun w => ((w.val : ℝ), 0), fun u _ t => ((u.val : ℝ) + t, 0), ?_, ?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq, and_true] at hab
    exact Fin.ext (by exact_mod_cast hab)
  · intro u v huv hadj
    have hv := path3_adj huv hadj
    refine ⟨by fun_prop, ?_, by simp, ?_, ?_⟩
    · intro a _ b _ hab
      simp only [Prod.mk.injEq, and_true, add_right_inj] at hab
      exact hab
    · simp [hv]
    · intro t ht w hw
      simp only [Prod.mk.injEq, and_true] at hw
      obtain ⟨h0, h1⟩ := ht
      have hlo : (u.val : ℝ) < w.val := by linarith
      have hhi : (w.val : ℝ) < u.val + 1 := by linarith
      have h2 : u.val < w.val := by exact_mod_cast hlo
      have h3 : w.val < u.val + 1 := by exact_mod_cast hhi
      omega
  · intro u v x y huv hxy hadj1 hadj2 hne t ht s hs heq
    have hv := path3_adj huv hadj1
    have hy := path3_adj hxy hadj2
    have hux : u.val ≠ x.val := by
      intro h
      apply hne
      have hu : u = x := Fin.ext h
      have hv' : v = y := Fin.ext (by omega)
      rw [hu, hv']
    simp only [Prod.mk.injEq, and_true] at heq
    obtain ⟨t0, t1⟩ := ht
    obtain ⟨s0, s1⟩ := hs
    have hu2 : u.val ≤ 1 := by have := v.isLt; omega
    have hx2 : x.val ≤ 1 := by have := y.isLt; omega
    rcases Nat.lt_or_gt_of_ne hux with h | h
    · have hu0 : u.val = 0 := by omega
      have hx1 : x.val = 1 := by omega
      rw [hu0, hx1] at heq
      push_cast at heq
      constructor
      · right; linarith
      · left; linarith
    · have hu0 : u.val = 1 := by omega
      have hx1 : x.val = 0 := by omega
      rw [hu0, hx1] at heq
      push_cast at heq
      constructor
      · left; linarith
      · right; linarith

theorem path3_edges : (SimpleGraph.pathGraph 3).edgeSet.ncard = 2 := by
  have : (SimpleGraph.pathGraph 3).edgeSet = {s(0, 1), s(1, 2)} := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [SimpleGraph.mem_edgeSet, SimpleGraph.pathGraph_adj, Set.mem_insert_iff,
        Set.mem_singleton_iff, Sym2.eq_iff]
      fin_cases a <;> fin_cases b <;> simp
  rw [this, Set.ncard_pair]
  decide

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard)
    (c : ℕ),
    L.edgeSet.ncard + 3 * c + 3 ≤ 3 * Fintype.card V) := by
  intro h
  have := h (SimpleGraph.pathGraph 3) (by simp) path3_drawing (by rw [path3_edges]) 2
  rw [path3_edges] at this
  simp at this
