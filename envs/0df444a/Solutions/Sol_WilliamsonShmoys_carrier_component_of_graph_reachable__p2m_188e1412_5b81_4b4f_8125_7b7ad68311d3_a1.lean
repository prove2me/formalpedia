-- Prove2me | solution 1 for WilliamsonShmoys.carrier_component_of_graph_reachable__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:25:39.516647+00:00
-- url     : https://prove2.me/submissions/9a1b26fb-03c8-4959-8059-b55dfb6550e0

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (point : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (_hp : Function.Injective point)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = point u ∧ arc u v 1 = point v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ point w)
    (_hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) :
    G.Reachable u v →
      point v ∈ connectedComponentIn
        (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G point arc)
        (point u) := by
  let C : Set (ℝ × ℝ) :=
    WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G point arc
  have edge_mem {a b : V} (hab : G.Adj a b) :
      point b ∈ connectedComponentIn C (point a) := by
    by_cases hablt : a < b
    · obtain ⟨hcont, _, h0, h1, _⟩ := ha a b hablt hab
      let S : Set (ℝ × ℝ) := arc a b '' Set.Icc (0 : ℝ) 1
      have hpre : IsPreconnected S := isPreconnected_Icc.image (arc a b) hcont
      have hsub : S ⊆ C := by
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        change (∃ w, arc a b t = point w) ∨
          ∃ x y, x < y ∧ G.Adj x y ∧ ∃ s ∈ Set.Icc (0 : ℝ) 1, arc a b t = arc x y s
        exact Or.inr ⟨a, b, hablt, hab, t, ht, rfl⟩
      have hstart : point a ∈ S := ⟨0, by norm_num, h0⟩
      have hend : point b ∈ S := ⟨1, by norm_num, h1⟩
      exact (hpre.subset_connectedComponentIn hstart hsub) hend
    · have hblt : b < a := lt_of_le_of_ne (le_of_not_gt hablt) (Ne.symm hab.ne)
      have hba : G.Adj b a := hab.symm
      obtain ⟨hcont, _, h0, h1, _⟩ := ha b a hblt hba
      let S : Set (ℝ × ℝ) := arc b a '' Set.Icc (0 : ℝ) 1
      have hpre : IsPreconnected S := isPreconnected_Icc.image (arc b a) hcont
      have hsub : S ⊆ C := by
        intro z hz
        rcases hz with ⟨t, ht, rfl⟩
        change (∃ w, arc b a t = point w) ∨
          ∃ x y, x < y ∧ G.Adj x y ∧ ∃ s ∈ Set.Icc (0 : ℝ) 1, arc b a t = arc x y s
        exact Or.inr ⟨b, a, hblt, hba, t, ht, rfl⟩
      have hstart : point b ∈ S := ⟨0, by norm_num, h0⟩
      have hend : point a ∈ S := ⟨1, by norm_num, h1⟩
      have hreach : point a ∈ connectedComponentIn C (point b) :=
        (hpre.subset_connectedComponentIn hstart hsub) hend
      have heq : connectedComponentIn C (point b) = connectedComponentIn C (point a) :=
        connectedComponentIn_eq hreach
      rw [← heq]
      exact mem_connectedComponentIn (hsub hstart)
  have walk_mem : ∀ {x y : V} (w : G.Walk x y),
      point y ∈ connectedComponentIn C (point x) := by
    intro x y w
    induction w with
    | nil =>
        apply mem_connectedComponentIn
        unfold C WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
        simp only [Set.mem_setOf_eq]
        exact Or.inl ⟨_, rfl⟩
    | @cons x y z hxy w ih =>
        have hxy' : point y ∈ connectedComponentIn C (point x) := edge_mem hxy
        have hcomp := connectedComponentIn_eq hxy'
        rw [← hcomp] at ih
        exact ih
  intro h
  rcases h with ⟨w⟩
  exact walk_mem w