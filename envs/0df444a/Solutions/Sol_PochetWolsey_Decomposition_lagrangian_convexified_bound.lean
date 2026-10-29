-- Prove2me | solution 1 for PochetWolsey.Decomposition.lagrangian_convexified_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:31:36.042001+00:00
-- url     : https://prove2.me/submissions/91bbe209-9054-4fb8-a4a1-dffff0c800ed

import Mathlib

theorem solution : ¬ (∀ {n m q t : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (D : Matrix (Fin q) (Fin n) ℝ) (d : Fin q → ℝ)
    (c : Fin n → ℝ)
    (B : Matrix (Fin t) (Fin n) ℝ) (e : Fin t → ℝ),
    let Y : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      (∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) ∧
      (∀ j, ∃ z : ℤ, x j = (z : ℝ))}
    let PZ : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, d i ≤ ∑ j, D i j * x j}
    let H := convexHull ℝ Y ∩ PZ
    let PYtight : Set (Fin n → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      ∀ i, e i ≤ ∑ j, B i j * x j}
    let cost : (Fin n → ℝ) → ℝ := fun x => ∑ j, c j * x j
    let lag : (Fin q → ℝ) → (Fin n → ℝ) → ℝ := fun π x =>
      cost x + ∑ i, π i * (d i - ∑ j, D i j * x j)
    let L : (Fin q → ℝ) → EReal := fun π =>
      sInf ((fun x => (lag π x : EReal)) '' Y)
    let master : Set (Fin n → ℝ) := {x | x ∈ PZ ∧
      ∃ (k r : ℕ) (v : Fin k → (Fin n → ℝ))
        (u : Fin r → (Fin n → ℝ)) (lam : Fin k → ℝ) (μ : Fin r → ℝ),
        (∀ a, v a ∈ Y) ∧
        (∀ a, u a ≠ 0 ∧ (∀ j, 0 ≤ u a j) ∧
          ∀ i, 0 ≤ ∑ j, (A i j : ℝ) * u a j) ∧
        (∀ a, 0 ≤ lam a) ∧ (∑ a, lam a) = 1 ∧ (∀ a, 0 ≤ μ a) ∧
        x = (fun j => (∑ a, lam a * v a j) + ∑ a, μ a * u a j)}
    let w : EReal := sInf ((fun x => (cost x : EReal)) '' H)
    let zLP : EReal := sSup ((fun x => (cost x : EReal)) '' (PYtight ∩ PZ))
    PYtight = convexHull ℝ Y → H.Nonempty → BddBelow (cost '' H) →
    ∃ (xstar ystar : Fin n → ℝ) (πstar : Fin q → ℝ),
      xstar ∈ H ∧ (∀ x ∈ H, cost xstar ≤ cost x) ∧
      (∀ i, 0 ≤ πstar i) ∧ ystar ∈ Y ∧
      (∀ y ∈ Y, lag πstar ystar ≤ lag πstar y) ∧
      w = (cost xstar : EReal) ∧
      w = L πstar ∧ (∀ π : Fin q → ℝ, (∀ i, 0 ≤ π i) → L π ≤ L πstar) ∧
      w = zLP ∧ w = sInf ((fun x => (cost x : EReal)) '' master) ∧
      xstar ∈ master ∧
      ∃ xmax ∈ PYtight ∩ PZ, (∀ x ∈ PYtight ∩ PZ, cost x ≤ cost xmax) ∧
        zLP = (cost xmax : EReal)) := by
  intro H
  have H1 := @H 1 1 0 1 (fun _ _ => -1) (fun _ => -1) (fun _ _ => 0) (fun _ => 0) (fun _ => 1)
    (fun _ _ => -1) (fun _ => -1)
  simp only at H1
  -- Y = {0, 1} and its hull is the unit box
  set Y : Set (Fin 1 → ℝ) := {x | (∀ j, 0 ≤ x j) ∧
      (∀ i : Fin 1, (((-1 : ℚ)) : ℝ) ≤ ∑ j, (((-1 : ℚ)) : ℝ) * x j) ∧
      (∀ j, ∃ z : ℤ, x j = (z : ℝ))} with hY
  have hbox : ∀ x : Fin 1 → ℝ, x ∈ convexHull ℝ Y ↔ 0 ≤ x 0 ∧ x 0 ≤ 1 := by
    intro x
    constructor
    · intro hx
      have hsub : convexHull ℝ Y ⊆ {y : Fin 1 → ℝ | 0 ≤ y 0 ∧ y 0 ≤ 1} := by
        apply convexHull_min
        · intro y ⟨h0, h1, _⟩
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
      have h0Y : (0 : Fin 1 → ℝ) ∈ Y := ⟨fun _ => le_rfl, fun _ => by simp, fun _ => ⟨0, by simp⟩⟩
      have h1Y : (1 : Fin 1 → ℝ) ∈ Y := ⟨fun _ => zero_le_one, fun _ => by simp, fun _ => ⟨1, by simp⟩⟩
      have hseg := segment_subset_convexHull (𝕜 := ℝ) h0Y h1Y
      apply hseg
      refine ⟨1 - x 0, x 0, by linarith, h0, by ring, ?_⟩
      ext j
      fin_cases j
      simp
  have hPY : {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 1), -1 ≤ ∑ j, -1 * x j} =
      convexHull ℝ Y := by
    ext x; rw [hbox]; simp
  have h0H : (0 : Fin 1 → ℝ) ∈ convexHull ℝ Y ∩
      {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 0), 0 ≤ ∑ j, 0 * x j} :=
    ⟨(hbox 0).mpr (by simp), fun _ => le_rfl, fun i => i.elim0⟩
  have h1P : (1 : Fin 1 → ℝ) ∈ {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 1), -1 ≤ ∑ j, -1 * x j} ∩
      {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 0), 0 ≤ ∑ j, 0 * x j} :=
    ⟨⟨fun _ => zero_le_one, fun _ => by simp⟩, fun _ => zero_le_one, fun i => i.elim0⟩
  have hbdd : BddBelow ((fun x : Fin 1 → ℝ => ∑ j, 1 * x j) '' (convexHull ℝ Y ∩
      {x : Fin 1 → ℝ | (∀ (j : Fin 1), 0 ≤ x j) ∧ ∀ (i : Fin 0), 0 ≤ ∑ j, 0 * x j})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, ⟨-, hx2⟩, rfl⟩
    simpa using hx2.1 0
  obtain ⟨xs, ys, πs, -, -, -, -, -, -, -, -, hwz, -⟩ := H1 hPY ⟨0, h0H⟩ hbdd
  have hA := sInf_le (Set.mem_image_of_mem (fun x : Fin 1 → ℝ => ((∑ j, 1 * x j : ℝ) : EReal)) h0H)
  have hB := le_sSup (Set.mem_image_of_mem (fun x : Fin 1 → ℝ => ((∑ j, 1 * x j : ℝ) : EReal)) h1P)
  rw [hwz] at hA
  have := le_trans hB hA
  simp at this
  exact (not_le.mpr zero_lt_one) this
