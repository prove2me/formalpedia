-- Prove2me | solution 1 for WilliamsonShmoys.drawing_carrier_is_compact__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:20.006361+00:00
-- url     : https://prove2.me/submissions/1c75e321-7932-443b-9cb6-76c905d0c7d6

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    IsCompact (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) := by
  classical
  let E := {q : V × V // q.1 < q.2 ∧ G.Adj q.1 q.2}
  let edge : E → Set (ℝ × ℝ) := fun q => arc q.1.1 q.1.2 '' Set.Icc (0 : ℝ) 1
  let pieces : V ⊕ E → Set (ℝ × ℝ) :=
    Sum.elim (fun w => {p w}) edge
  have hpieces :
      WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc =
        ⋃ i, pieces i := by
    ext z
    constructor
    · intro hz
      change (∃ w, z = p w) ∨
        ∃ u v, u < v ∧ G.Adj u v ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, z = arc u v t at hz
      rcases hz with ⟨w, hzw⟩ | ⟨u, v, huv, hadj, t, ht, hzt⟩
      · apply Set.mem_iUnion.2
        refine ⟨Sum.inl w, ?_⟩
        change z ∈ {p w}
        exact Set.mem_singleton_iff.2 hzw
      · let q : E := ⟨(u, v), huv, hadj⟩
        apply Set.mem_iUnion.2
        refine ⟨Sum.inr q, ?_⟩
        change z ∈ arc u v '' Set.Icc (0 : ℝ) 1
        rw [hzt]
        exact Set.mem_image_of_mem (arc u v) ht
    · intro hz
      rcases Set.mem_iUnion.1 hz with ⟨i, hmem⟩
      cases i with
      | inl w =>
          have hzw : z = p w := by
            simpa [pieces] using hmem
          change (∃ w, z = p w) ∨
            ∃ u v, u < v ∧ G.Adj u v ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, z = arc u v t
          exact Or.inl ⟨w, hzw⟩
      | inr q =>
          change z ∈ arc q.1.1 q.1.2 '' Set.Icc (0 : ℝ) 1 at hmem
          change ∃ t ∈ Set.Icc (0 : ℝ) 1, arc q.1.1 q.1.2 t = z at hmem
          rcases hmem with ⟨t, ht, htz⟩
          change (∃ w, z = p w) ∨
            ∃ u v, u < v ∧ G.Adj u v ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, z = arc u v t
          exact Or.inr ⟨q.1.1, q.1.2, q.2.1, q.2.2, t, ht, htz.symm⟩
  rw [hpieces]
  apply isCompact_iUnion
  intro i
  cases i with
  | inl w =>
      simpa [pieces] using (isCompact_singleton : IsCompact ({p w} : Set (ℝ × ℝ)))
  | inr q =>
      dsimp [pieces, edge]
      exact isCompact_Icc.image_of_continuousOn
        ((ha q.1.1 q.1.2 q.2.1 q.2.2).1)
