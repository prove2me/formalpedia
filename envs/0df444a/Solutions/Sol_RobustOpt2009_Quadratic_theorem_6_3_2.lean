-- Prove2me | solution 1 for RobustOpt2009.Quadratic.theorem_6_3_2
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:21:38.579646+00:00
-- url     : https://prove2.me/submissions/f39de8b8-7a8b-4c0e-8d61-ad8accf9f015

import Mathlib

open Matrix
open scoped BigOperators

theorem solution : ¬ (∀ {n k p q m r s : ℕ} (hp : 0 < p) (hq : 0 < q)
    (K : Set (Fin m → ℝ)) (P : Matrix (Fin m) (Fin r) ℝ)
    (Q : Matrix (Fin m) (Fin s) ℝ) (c : Fin m → ℝ)
    (hclosed : IsClosed {χ : Fin r → ℝ | ∃ u, P *ᵥ χ + Q *ᵥ u + c ∈ K})
    (hreg :
      ((K.Nonempty ∧ (∀ z ∈ K, ∀ w ∈ K, z + w ∈ K) ∧
        (∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → t • z ∈ K)) ∧
        (∀ z ∈ K, -z ∈ K → z = 0) ∧ IsClosed K ∧
        ∃ χ u, P *ᵥ χ + Q *ᵥ u + c ∈ interior K) ∨
      (∃ (h : ℕ) (H : Matrix (Fin h) (Fin m) ℝ),
        K = {z | ∀ i, 0 ≤ (H *ᵥ z) i}))
    (An : Matrix (Fin k) (Fin n) ℝ) (bn : Fin k → ℝ)
    (σ : (Fin n → ℝ) →ᵃ[ℝ] (Fin r → ℝ)) (δ : (Fin n → ℝ) →ᵃ[ℝ] ℝ),
    let norm₂ : {d : ℕ} → (Fin d → ℝ) → ℝ := fun {_} x => Real.sqrt (∑ i, x i ^ 2)
    let Z : Set (Fin r → ℝ) := {χ | ∃ u, P *ᵥ χ + Q *ᵥ u + c ∈ K}
    (∀ (L : (Fin n → ℝ) →ᵃ[ℝ] Matrix (Fin p) (Fin k) ℝ)
      (R : Fin q → ℝ), R ≠ 0 → ∀ y : Fin n → ℝ,
      ((∀ η : Matrix (Fin p) (Fin q) ℝ,
        (∀ u : Fin q → ℝ, norm₂ (η *ᵥ u) ≤ norm₂ u) →
        ∀ χ ∈ Z, norm₂ (An *ᵥ y + bn + (L y)ᵀ *ᵥ (η *ᵥ R)) ≤ σ y ⬝ᵥ χ + δ y) ↔
        ∃ (τ : ℝ) (v : Fin m → ℝ) (lam : ℝ),
          (τ + c ⬝ᵥ v ≤ δ y ∧ Pᵀ *ᵥ v = σ y ∧ Qᵀ *ᵥ v = 0 ∧
            ∀ z ∈ K, 0 ≤ v ⬝ᵥ z) ∧
          (Matrix.fromBlocks
            (Matrix.fromBlocks (τ • (1 : Matrix (Fin k) (Fin k) ℝ)) (L y)ᵀ (L y)
              (lam • (1 : Matrix (Fin p) (Fin p) ℝ)))
            (fun i (_ : Unit) => Sum.elim (An *ᵥ y + bn) (fun _ => 0) i)
            (fun (_ : Unit) j => Sum.elim (An *ᵥ y + bn) (fun _ => 0) j)
            (fun (_ : Unit) (_ : Unit) => τ - lam * (R ⬝ᵥ R))).PosSemidef)) ∧
    (∀ (L : Matrix (Fin p) (Fin k) ℝ), L ≠ 0 →
      ∀ (R : (Fin n → ℝ) →ᵃ[ℝ] (Fin q → ℝ)) (y : Fin n → ℝ),
      ((∀ η : Matrix (Fin p) (Fin q) ℝ,
        (∀ u : Fin q → ℝ, norm₂ (η *ᵥ u) ≤ norm₂ u) →
        ∀ χ ∈ Z, norm₂ (An *ᵥ y + bn + Lᵀ *ᵥ (η *ᵥ R y)) ≤ σ y ⬝ᵥ χ + δ y) ↔
        ∃ (τ : ℝ) (v : Fin m → ℝ) (lam : ℝ),
          (τ + c ⬝ᵥ v ≤ δ y ∧ Pᵀ *ᵥ v = σ y ∧ Qᵀ *ᵥ v = 0 ∧
            ∀ z ∈ K, 0 ≤ v ⬝ᵥ z) ∧
          (Matrix.fromBlocks
            (Matrix.fromBlocks (τ • (1 : Matrix (Fin k) (Fin k) ℝ) - lam • (Lᵀ * L))
              (0 : Matrix (Fin k) (Fin q) ℝ) (0 : Matrix (Fin q) (Fin k) ℝ)
              (lam • (1 : Matrix (Fin q) (Fin q) ℝ)))
            (fun i (_ : Unit) => Sum.elim (An *ᵥ y + bn) (R y) i)
            (fun (_ : Unit) j => Sum.elim (An *ᵥ y + bn) (R y) j)
            (fun (_ : Unit) (_ : Unit) => τ)).PosSemidef))) := by
  intro h
  have hZ : {χ : Fin 1 → ℝ | ∃ u, (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ χ + (0 : Matrix (Fin 1) (Fin 0) ℝ) *ᵥ u + (fun _ => -1) ∈
      {z : Fin 1 → ℝ | ∀ i, 0 ≤ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ z) i}} = ∅ := by
    ext χ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, hu⟩
    have := hu 0
    simp at this
    linarith
  have H := h (n := 0) (k := 0) (p := 1) (q := 1) (m := 1) (r := 1) (s := 0) one_pos one_pos
    {z : Fin 1 → ℝ | ∀ i, 0 ≤ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ z) i} 0 0 (fun _ => -1)
    (by rw [hZ]; exact isClosed_empty) (Or.inr ⟨1, 1, rfl⟩) 0 0
    (AffineMap.const ℝ _ (fun _ => 1)) (AffineMap.const ℝ _ 0)
  have H1 := (H.1 (AffineMap.const ℝ _ 0) (fun _ => 1) (by
    intro h0; have := congrFun h0 0; simp at this) 0).1 (by
    intro η _ χ hχ
    exfalso
    have : χ ∈ ({χ : Fin 1 → ℝ | ∃ u, (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ χ + (0 : Matrix (Fin 1) (Fin 0) ℝ) *ᵥ u + (fun _ => -1) ∈
      {z : Fin 1 → ℝ | ∀ i, 0 ≤ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ z) i}} : Set _) := hχ
    rw [hZ] at this
    exact this)
  obtain ⟨τ, v, lam, ⟨_, hP, _⟩, _⟩ := H1
  have := congrFun hP 0
  simp at this
