-- Prove2me | solution 1 for PochetWolsey.Reformulation.zero_inventory_optimal
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:26:24.875321+00:00
-- url     : https://prove2.me/submissions/57e48003-3bcf-49f4-8a96-dc3b01c17b9c

import Mathlib

theorem solution : ¬ (∀ (n : ℕ) (hn : 0 < n) (d p q : Fin n → ℝ) (h : Fin (n + 1) → ℝ)
    (hd : ∀ t, 0 ≤ d t) (M : ℝ) (hM : 0 < M) (hlarge : (∑ t, d t) ≤ M),
    let P : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z.2.1 0 = 0 ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ t, 0 ≤ z.2.2 t ∧ z.2.2 t ≤ 1 ∧
          z.2.1 t.castSucc + z.1 t = d t + z.2.1 t.succ ∧
          z.1 t ≤ M * z.2.2 t)}
    let X := {z | z ∈ P ∧ ∀ t, z.2.2 t = 0 ∨ z.2.2 t = 1}
    let cost := fun z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (∑ t, p t * z.1 t) + (∑ k, h k * z.2.1 k) + (∑ t, q t * z.2.2 t)
    ∃ z ∈ X, (∀ z' ∈ X, cost z ≤ cost z') ∧
      ∀ t, z.2.1 t.castSucc * z.1 t = 0) := by
  intro H
  have H2 := H 2 (by norm_num) (fun _ => 0) (fun _ => 0) (fun _ => 0) ![0, -1, 0] (fun _ => le_rfl)
    1 one_pos (by simp)
  simp only at H2
  obtain ⟨z, ⟨⟨hs0, hs2, hsnn, hrow⟩, hbin⟩, hmin, hz⟩ := H2
  have r0 := hrow 0
  have r1 := hrow 1
  have hm := hmin (![1, -1], ![0, 1, 0], ![1, 1])
    ⟨⟨by simp, by simp, by intro k; fin_cases k <;> simp, by intro t; fin_cases t <;> simp⟩,
      by intro t; fin_cases t <;> simp⟩
  have hz1 := hz 1
  simp [Fin.sum_univ_succ] at hm r0 r1 hz1 hs2
  rcases hz1 with h | h <;> linarith [r1.2.2.1]
