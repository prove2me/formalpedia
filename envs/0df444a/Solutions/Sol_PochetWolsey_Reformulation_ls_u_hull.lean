-- Prove2me | solution 1 for PochetWolsey.Reformulation.ls_u_hull
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:26:28.221635+00:00
-- url     : https://prove2.me/submissions/9f96e64c-9a95-4787-bb59-63a26cc91469

import Mathlib

theorem solution : ¬ (∀ (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (M : ℝ) (hM : 0 < M) (hlarge : (∑ t, d t) ≤ M),
    let P : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z.2.1 0 = 0 ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ t, 0 ≤ z.2.2 t ∧ z.2.2 t ≤ 1 ∧
          z.2.1 t.castSucc + z.1 t = d t + z.2.1 t.succ ∧
          z.1 t ≤ M * z.2.2 t)}
    let X := {z | z ∈ P ∧ ∀ t, z.2.2 t = 0 ∨ z.2.2 t = 1}
    convexHull ℝ X =
      {z | z ∈ P ∧ ∀ (l : Fin n) (S : Finset (Fin n)),
        (∀ j ∈ S, j ≤ l) →
          (∑ j ∈ S, z.1 j) ≤
            (∑ j ∈ S, (∑ k ∈ Finset.Icc j l, d k) * z.2.2 j) + z.2.1 l.succ}) := by
  intro H
  have H2 := H 2 (by norm_num) (fun _ => 0) (fun _ => le_rfl) 1 one_pos (by simp)
  simp only at H2
  have hz := (Set.ext_iff.mp H2
    ((![1, -1], ![0, 1, 0], ![1, 1]) : (Fin 2 → ℝ) × (Fin 3 → ℝ) × (Fin 2 → ℝ))).mp
    (subset_convexHull ℝ _
      ⟨⟨by simp, by simp, by intro k; fin_cases k <;> simp, by intro t; fin_cases t <;> simp⟩,
        by intro t; fin_cases t <;> simp⟩)
  have := hz.2 1 {0} (by intro j hj; simp at hj; subst hj; decide)
  simp at this
  norm_num at this
