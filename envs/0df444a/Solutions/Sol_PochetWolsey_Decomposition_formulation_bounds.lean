-- Prove2me | solution 1 for PochetWolsey.Decomposition.formulation_bounds
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:02:44.657969+00:00
-- url     : https://prove2.me/submissions/dfbdbb3e-cf5a-4b92-8c53-9c5534bde223

import Mathlib

theorem solution : ¬ (∀ {n m q t p a s : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (D : Matrix (Fin q) (Fin n) ℝ) (d : Fin q → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin t) (Fin n) ℝ) (e : Fin t → ℝ)
    (F : Matrix (Fin a) (Fin n) ℝ) (G : Matrix (Fin a) (Fin p) ℝ)
    (g : Fin a → ℝ)
    (cuts : Matrix (Fin s) (Fin n) ℝ) (rhs : Fin s → ℝ)
    (sep : (Fin n → ℝ) → Option ((Fin n → ℝ) × ℝ)),
    let PY : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j}
    let Y : Set (Fin n → ℝ) := {x | x ∈ PY ∧ ∀ j, ∃ z : ℤ, x j = (z : ℝ)}
    let PZ : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, d i ≤ ∑ j, D i j * x j}
    let direct : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, e i ≤ ∑ j, B i j * x j}
    let Q : Set ((Fin n → ℝ) × (Fin p → ℝ)) := {xv |
      (∀ j, 0 ≤ xv.1 j) ∧
      ∀ i, g i ≤ (∑ j, F i j * xv.1 j) + ∑ j, G i j * xv.2 j}
    let projection : Set (Fin n → ℝ) := {x | ∃ v : Fin p → ℝ, (x, v) ∈ Q}
    let cutting : Set (Fin n → ℝ) := {x | x ∈ PY ∩ PZ ∧
      ∀ i, rhs i ≤ ∑ j, cuts i j * x j}
    let cost : (Fin n → ℝ) → ℝ := fun x => ∑ j, c j * x j
    let value : Set (Fin n → ℝ) → EReal := fun S =>
      sSup ((fun x => (cost x : EReal)) '' S)
    direct = convexHull ℝ Y → projection = convexHull ℝ Y →
    (∀ i, ∀ y ∈ Y, rhs i ≤ ∑ j, cuts i j * y j) →
    (∀ x, sep x = none ↔ x ∈ convexHull ℝ Y) →
    (∀ x α β, sep x = some (α, β) →
      (∀ y ∈ Y, β ≤ ∑ j, α j * y j) ∧ (∑ j, α j * x j) < β) →
    (∃ xbar ∈ cutting, (∀ x ∈ cutting, cost xbar ≤ cost x) ∧ sep xbar = none) →
    value (direct ∩ PZ) = value (projection ∩ PZ) ∧
    value (projection ∩ PZ) = value cutting ∧
    value cutting = sInf ((fun x => (cost x : EReal)) '' (convexHull ℝ Y ∩ PZ)) ∧
    (∀ S ∈ [direct ∩ PZ, projection ∩ PZ, cutting],
      ∃ xmax ∈ S, (∀ x ∈ S, cost x ≤ cost xmax) ∧ value S = (cost xmax : EReal)) ∧
    ∃ xstar ∈ convexHull ℝ Y ∩ PZ,
      (∀ x ∈ convexHull ℝ Y ∩ PZ, cost xstar ≤ cost x) ∧
      sInf ((fun x => (cost x : EReal)) '' (convexHull ℝ Y ∩ PZ)) =
        (cost xstar : EReal)) := by
  intro H
  let sep : (Fin 1 → ℝ) → Option ((Fin 1 → ℝ) × ℝ) := fun x =>
    if x 0 < 0 then some (fun _ => 1, 0) else if 1 < x 0 then some (fun _ => -1, -1) else none
  have H1 := @H 1 1 0 1 0 1 0 (fun _ _ => -1) (fun _ => -1) (fun _ _ => 0) (fun _ => 0) (fun _ => 1)
    (fun _ _ => -1) (fun _ => -1) (fun _ _ => -1) (fun _ _ => 0) (fun _ => -1) (fun _ _ => 0)
    (fun _ => 0) sep
  simp only at H1
  set Y : Set (Fin 1 → ℝ) := {x | x ∈ {x : Fin 1 → ℝ | (∀ j, 0 ≤ x j) ∧
      (∀ i : Fin 1, (((-1 : ℚ)) : ℝ) ≤ ∑ j, (((-1 : ℚ)) : ℝ) * x j)} ∧
      (∀ j, ∃ z : ℤ, x j = (z : ℝ))} with hY
  have hbox : ∀ x : Fin 1 → ℝ, x ∈ convexHull ℝ Y ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
    intro x
    constructor
    · intro hx
      have hsub : convexHull ℝ Y ⊆ {y : Fin 1 → ℝ | 0 ≤ y 0 ∧ y 0 ≤ 1} := by
        apply convexHull_min
        · intro y ⟨⟨h0, h1⟩, _⟩
          have := h1 0
          simp at this
          exact ⟨h0 0, by linarith⟩
        · intro a ha b hb μ ν hμ hν hμν
          simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
          constructor
          · nlinarith [ha.1, hb.1]
          · nlinarith [ha.2, hb.2]
      exact hsub hx
    · rintro ⟨h0, h1⟩
      have h0Y : (0 : Fin 1 → ℝ) ∈ Y := ⟨⟨fun _ => le_rfl, fun _ => by simp⟩, fun _ => ⟨0, by simp⟩⟩
      have h1Y : (1 : Fin 1 → ℝ) ∈ Y := ⟨⟨fun _ => zero_le_one, fun _ => by simp⟩, fun _ => ⟨1, by simp⟩⟩
      have hseg := segment_subset_convexHull (𝕜 := ℝ) h0Y h1Y
      apply hseg
      refine ⟨1 - x 0, x 0, by linarith, h0, by ring, ?_⟩
      ext j
      fin_cases j
      simp
  have hYbox : ∀ y ∈ Y, 0 ≤ y 0 ∧ y 0 ≤ 1 := fun y hy => (hbox y).mp (subset_convexHull ℝ Y hy)
  refine absurd (H1 ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · ext x; rw [hbox]; simp
  · ext x; rw [hbox]; simp
  · intro i; exact i.elim0
  · intro x; rw [hbox]; simp only [sep]
    split_ifs with h1 h2
    · constructor
      · intro h; exact absurd h (by simp)
      · intro h; linarith [h.1]
    · constructor
      · intro h; exact absurd h (by simp)
      · intro h; linarith [h.2]
    · exact ⟨fun _ => ⟨not_lt.mp h1, not_lt.mp h2⟩, fun _ => rfl⟩
  · intro x α β h
    simp only [sep] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun y hy => ?_, ?_⟩
      · simpa using (hYbox y hy).1
      · simpa using h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun y hy => ?_, ?_⟩
      · simp; linarith [(hYbox y hy).2]
      · simp; linarith
  · refine ⟨0, ⟨⟨⟨fun _ => le_rfl, fun _ => by simp⟩, fun _ => le_rfl, fun i => i.elim0⟩, fun i => i.elim0⟩,
      ?_, by simp [sep]⟩
    rintro x ⟨⟨⟨hx0, -⟩, -⟩, -⟩
    simpa using hx0 0
  · rintro ⟨-, -, h3, -⟩
    have h0H : (0 : Fin 1 → ℝ) ∈ convexHull ℝ Y ∩
        {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 0), 0 ≤ ∑ j, 0 * x j} :=
      ⟨(hbox 0).mpr (by simp), fun _ => le_rfl, fun i => i.elim0⟩
    have h1C : (1 : Fin 1 → ℝ) ∈ {x : Fin 1 → ℝ | x ∈ {x : Fin 1 → ℝ | (∀ j, 0 ≤ x j) ∧
        (∀ i : Fin 1, (((-1 : ℚ)) : ℝ) ≤ ∑ j, (((-1 : ℚ)) : ℝ) * x j)} ∩
        {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 0), 0 ≤ ∑ j, 0 * x j} ∧
        ∀ (i : Fin 0), 0 ≤ ∑ j, 0 * x j} :=
      ⟨⟨⟨fun _ => zero_le_one, fun _ => by simp⟩, fun _ => zero_le_one, fun i => i.elim0⟩,
        fun i => i.elim0⟩
    have hA := sInf_le (Set.mem_image_of_mem (fun x : Fin 1 → ℝ => ((∑ j, 1 * x j : ℝ) : EReal)) h0H)
    have hB := le_sSup (Set.mem_image_of_mem (fun x : Fin 1 → ℝ => ((∑ j, 1 * x j : ℝ) : EReal)) h1C)
    rw [← h3] at hA
    have := le_trans hB hA
    simp at this
    exact (not_le.mpr zero_lt_one) this
