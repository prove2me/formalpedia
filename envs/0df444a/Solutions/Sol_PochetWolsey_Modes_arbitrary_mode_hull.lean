-- Prove2me | solution 1 for PochetWolsey.Modes.arbitrary_mode_hull
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:25:04.161324+00:00
-- url     : https://prove2.me/submissions/c1b6c919-468d-46a3-9d54-36fd81101823

import Mathlib

theorem solution : ¬ (∀ (m n : ℕ),
    convexHull ℝ ({p : ((Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ) × (Fin (m + 1) → Fin (n + 1) → ℝ)) | ∃ s : Fin (n + 1) → List (Fin (m + 1)),
      (∀ t, s t ≠ [] ∧ (s t).Nodup) ∧
      (∀ t : Fin n, (s t.castSucc).getLast? = (s t.succ).head?) ∧ p = ((fun i t => if i ∈ s t then (1 : ℝ) else 0), (fun i t => if i ∈ (s t).tail then (1 : ℝ) else 0), (fun i t => if i ∈ (s t).dropLast then (1 : ℝ) else 0))}) =
    {p | ∃ φ : (Fin (m + 1) → Fin (n + 1) → ℝ),
    (∀ i, (∀ t, 0 ≤ p.1 i t ∧ p.1 i t ≤ 1)) ∧
  (∀ i, (∀ t, 0 ≤ p.2.1 i t ∧ p.2.1 i t ≤ 1)) ∧
  (∀ i, (∀ t, 0 ≤ p.2.2 i t ∧ p.2.2 i t ≤ 1)) ∧
  (∀ i, (∀ t, 0 ≤ φ i t ∧ φ i t ≤ 1)) ∧
  (∀ t, ∑ j, (p.1 j t - p.2.1 j t) = 1) ∧
  (∀ i (t : Fin n), p.1 i t.succ - p.2.1 i t.succ =
    p.1 i t.castSucc - p.2.2 i t.castSucc) ∧
  (∀ i t, p.1 i t - p.2.1 i t ≥ φ i t) ∧
  (∀ i t, p.1 i t - p.2.2 i t ≥ φ i t) ∧
  (∀ i t, φ i t ≥ p.1 i t - p.2.1 i t - p.2.2 i t) ∧
  (∀ i t, p.1 i t + ∑ j ∈ Finset.univ.erase i, φ j t ≤ 1)}) := by
  intro H
  have e := Set.ext_iff.mp (H 0 0)
  let p : (Fin 1 → Fin 1 → ℝ) × (Fin 1 → Fin 1 → ℝ) × (Fin 1 → Fin 1 → ℝ) :=
    (fun _ _ => 1, fun _ _ => 0, fun _ _ => 1)
  have hmem := (e p).mpr (by
    refine ⟨fun _ _ => 0, ?_⟩
    refine ⟨fun _ _ => ⟨zero_le_one, le_rfl⟩, fun _ _ => ⟨le_rfl, zero_le_one⟩,
      fun _ _ => ⟨zero_le_one, le_rfl⟩, fun _ _ => ⟨le_rfl, zero_le_one⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t; simp [p]
    · intro i t; exact t.elim0
    · intro i t; simp [p]
    · intro i t; simp [p]
    · intro i t; simp [p]
    · intro i t; simp [p])
  refine absurd (convexHull_min (𝕜 := ℝ)
      (t := {q : (Fin 1 → Fin 1 → ℝ) × (Fin 1 → Fin 1 → ℝ) × (Fin 1 → Fin 1 → ℝ) | q.2.2 0 0 = 0})
      ?_ ?_ hmem) ?_
  · rintro q ⟨s, hs, -, rfl⟩
    obtain ⟨hne, hnd⟩ := hs 0
    have hlen : (s 0).length ≤ 1 := by
      have := hnd.length_le_card; simpa using this
    have hd : (s 0).dropLast = [] := by
      rw [← List.length_eq_zero_iff, List.length_dropLast]; omega
    simp [hd]
  · intro a ha b hb μ ν _ _ _
    simp only [Set.mem_setOf_eq, Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at *
    rw [ha, hb]; ring
  · simp [p]
