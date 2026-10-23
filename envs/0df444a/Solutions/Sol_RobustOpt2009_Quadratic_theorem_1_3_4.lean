-- Prove2me | solution 1 for RobustOpt2009.Quadratic.theorem_1_3_4
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:59:42.872012+00:00
-- url     : https://prove2.me/submissions/264b200c-564f-4e0f-a9f1-52ffd4774f63

import Mathlib

open Matrix
open scoped BigOperators

theorem solution : ¬ (∀ {n m r s : ℕ} (K : Set (Fin m → ℝ)),
    ((K.Nonempty ∧ (∀ z ∈ K, ∀ w ∈ K, z + w ∈ K) ∧
      (∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → t • z ∈ K)) ∧
      (∀ z ∈ K, -z ∈ K → z = 0) ∧ IsClosed K ∧ (interior K).Nonempty) →
    ∀ (P : Matrix (Fin m) (Fin r) ℝ) (Q : Matrix (Fin m) (Fin s) ℝ)
    (c : Fin m → ℝ),
    ((∃ (h : ℕ) (H : Matrix (Fin h) (Fin m) ℝ),
      K = {z | ∀ i, 0 ≤ (H *ᵥ z) i}) ∨
      ∃ ζ u, P *ᵥ ζ + Q *ᵥ u + c ∈ interior K) →
    ∀ (a0 : Fin n → ℝ) (b0 : ℝ) (a : Fin r → Fin n → ℝ) (b : Fin r → ℝ)
    (x : Fin n → ℝ),
    ((∀ ζ : Fin r → ℝ, (∃ u, P *ᵥ ζ + Q *ᵥ u + c ∈ K) →
      (a0 + ∑ l, ζ l • a l) ⬝ᵥ x ≤ b0 + ζ ⬝ᵥ b) ↔
    ∃ v : Fin m → ℝ,
      c ⬝ᵥ v + a0 ⬝ᵥ x ≤ b0 ∧ Qᵀ *ᵥ v = 0 ∧
      (∀ l, (Pᵀ *ᵥ v) l + a l ⬝ᵥ x = b l) ∧
      (∀ z ∈ K, 0 ≤ v ⬝ᵥ z))) := by
  intro H
  set K : Set (Fin 1 → ℝ) := {z | 0 ≤ z 0} with hKdef
  have hK : (K.Nonempty ∧ (∀ z ∈ K, ∀ w ∈ K, z + w ∈ K) ∧
      (∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → t • z ∈ K)) ∧
      (∀ z ∈ K, -z ∈ K → z = 0) ∧ IsClosed K ∧ (interior K).Nonempty := by
    refine ⟨⟨⟨0, show (0 : ℝ) ≤ (0 : Fin 1 → ℝ) 0 from le_rfl⟩, fun z hz w hw => ?_, fun z hz t ht => ?_⟩, fun z hz hnz => ?_, ?_, ?_⟩
    · show 0 ≤ (z + w) 0; simp only [Pi.add_apply]; exact add_nonneg hz hw
    · show 0 ≤ (t • z) 0; simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg ht hz
    · have h1 : 0 ≤ z 0 := hz
      have h2 : 0 ≤ (-z) 0 := hnz
      simp only [Pi.neg_apply] at h2
      funext i; fin_cases i; simp; linarith
    · exact isClosed_le continuous_const (continuous_apply 0)
    · refine ⟨fun _ => 1, ?_⟩
      have ho : IsOpen {z : Fin 1 → ℝ | 0 < z 0} := isOpen_lt continuous_const (continuous_apply 0)
      have hsub : {z : Fin 1 → ℝ | 0 < z 0} ⊆ K := fun z (hz : 0 < z 0) => show 0 ≤ z 0 from le_of_lt hz
      exact interior_mono hsub (ho.interior_eq.symm ▸ (show (0 : ℝ) < 1 from one_pos))
  have hreg : (∃ (h : ℕ) (H : Matrix (Fin h) (Fin 1) ℝ),
      K = {z | ∀ i, 0 ≤ (H *ᵥ z) i}) ∨
      ∃ ζ u, (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ζ + (0 : Matrix (Fin 1) (Fin 0) ℝ) *ᵥ u +
        (fun _ => (-1 : ℝ)) ∈ interior K := by
    left
    refine ⟨1, 1, ?_⟩
    ext z
    simp only [one_mulVec, Set.mem_ofPred_eq, hKdef]
    constructor
    · intro h i; fin_cases i; exact h
    · intro h; exact h 0
  have := @H 0 1 1 0 K hK 0 0 (fun _ => -1) hreg 0 0 0 (fun _ => 1) 0
  have hlhs : ∀ ζ : Fin 1 → ℝ, (∃ u, (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ζ +
      (0 : Matrix (Fin 1) (Fin 0) ℝ) *ᵥ u + (fun _ => (-1 : ℝ)) ∈ K) →
      ((0 : Fin 0 → ℝ) + ∑ l, ζ l • (0 : Fin 1 → Fin 0 → ℝ) l) ⬝ᵥ (0 : Fin 0 → ℝ) ≤
        0 + ζ ⬝ᵥ (fun _ => (1 : ℝ)) := by
    rintro ζ ⟨u, hu⟩
    simp [hKdef] at hu
    linarith
  obtain ⟨v, _, _, hl, _⟩ := this.mp hlhs
  have := hl 0
  simp at this
