-- Prove2me | solution 1 for RobustOpt2009.Quadratic.lemma_6_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:42:24.293585+00:00
-- url     : https://prove2.me/submissions/47fa3755-90a8-47f8-ad1a-109b8a4c1ac5

import Mathlib
import Definitions.Def_RobustOpt2009_Quadratic_Setup

open Matrix

theorem g78r_qf {k : ℕ} (y : Fin k → ℝ) (t : ℝ) (x : Unit ⊕ Fin k → ℝ) :
    star x ⬝ᵥ (Matrix.fromBlocks (fun _ _ => t) (fun _ j => y j) (fun i _ => y i)
      (t • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ x) =
    t * x (Sum.inl ()) ^ 2 + 2 * x (Sum.inl ()) * ∑ i, y i * x (Sum.inr i) +
      t * ∑ i, x (Sum.inr i) ^ 2 := by
  set M : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ := Matrix.fromBlocks (fun _ _ => t)
    (fun _ j => y j) (fun i _ => y i) (t • (1 : Matrix (Fin k) (Fin k) ℝ)) with hM
  have h11 : ∀ a b : Unit, M (Sum.inl a) (Sum.inl b) = t := fun a b => by simp [hM, Matrix.fromBlocks]
  have h12 : ∀ (a : Unit) j, M (Sum.inl a) (Sum.inr j) = y j := fun a j => by simp [hM, Matrix.fromBlocks]
  have h21 : ∀ i (b : Unit), M (Sum.inr i) (Sum.inl b) = y i := fun i b => by simp [hM, Matrix.fromBlocks]
  have h22 : ∀ i j, M (Sum.inr i) (Sum.inr j) = if i = j then t else 0 := fun i j => by
    simp [hM, Matrix.fromBlocks, Matrix.one_apply]
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, h11, h12, h21, h22, star_trivial,
    Finset.univ_unique, Finset.sum_singleton, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [show (default : Unit) = () from rfl]
  have e1 : ∑ i, x (Sum.inr i) * (y i * x (Sum.inl ()) + t * x (Sum.inr i)) =
      x (Sum.inl ()) * ∑ i, y i * x (Sum.inr i) + t * ∑ i, x (Sum.inr i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, y i * x (Sum.inr i) = ∑ i, y i * x (Sum.inr i) := rfl
  rw [e1]
  have e3 : x (Sum.inl ()) * (t * x (Sum.inl ()) + ∑ j, y j * x (Sum.inr j)) =
      t * x (Sum.inl ()) ^ 2 + x (Sum.inl ()) * ∑ i, y i * x (Sum.inr i) := by ring
  rw [e3]; ring

theorem g78r_arrow {k : ℕ} (y : Fin k → ℝ) (t : ℝ) :
    Real.sqrt (∑ i, y i ^ 2) ≤ t ↔
      (Matrix.fromBlocks (fun _ _ => t) (fun _ j => y j) (fun i _ => y i)
        (t • (1 : Matrix (Fin k) (Fin k) ℝ)) : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ).PosSemidef := by
  set s := ∑ i, y i ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hherm : (Matrix.fromBlocks (fun _ _ => t) (fun _ j => y j) (fun i _ => y i)
      (t • (1 : Matrix (Fin k) (Fin k) ℝ)) : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℝ).IsHermitian := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [conjTranspose_apply, Matrix.one_apply, eq_comm, Matrix.fromBlocks]
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨hherm, fun x => ?_⟩
    rw [g78r_qf]
    set a := x (Sum.inl ())
    set q := ∑ i, x (Sum.inr i) ^ 2
    set p := ∑ i, y i * x (Sum.inr i)
    have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hcs : p ^ 2 ≤ s * q := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y (fun i => x (Sum.inr i))
      simpa [p, s, q] using this
    have ht : 0 ≤ t := (Real.sqrt_nonneg _).trans h
    have hst : s ≤ t ^ 2 := by
      have := Real.sq_sqrt hs0
      nlinarith [Real.sqrt_nonneg s]
    rcases ht.lt_or_eq with ht' | ht'
    · have : 0 ≤ t * (t * a ^ 2 + 2 * a * p + t * q) := by
        nlinarith [sq_nonneg (t * a + p), mul_nonneg (sub_nonneg.2 hst) hq]
      exact (mul_nonneg_iff_of_pos_left ht').1 this
    · subst ht'
      have hs' : s = 0 := le_antisymm (by simpa using hst) hs0
      have : p ^ 2 ≤ 0 := by rw [hs', zero_mul] at hcs; exact hcs
      have hp : p = 0 := by nlinarith [sq_nonneg p]
      rw [hp]; simp
  · rintro ⟨-, h⟩
    have ht : 0 ≤ t := by
      have := h (Pi.single (Sum.inl ()) 1)
      rw [g78r_qf] at this
      simpa using this
    set S := Real.sqrt s
    let x : Unit ⊕ Fin k → ℝ := fun z => match z with
      | Sum.inl _ => S
      | Sum.inr i => -y i
    have := h x
    rw [g78r_qf] at this
    simp only [x] at this
    have hS2 : S ^ 2 = s := Real.sq_sqrt hs0
    have e1 : ∑ i, y i * -y i = -s := by
      rw [hs, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (-y i) ^ 2 = s := by
      rw [hs]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at this
    -- this : 0 ≤ t * S^2 + 2 * S * (-s) + t * s = 2 s (t - S)
    rcases hs0.lt_or_eq with hsp | hsz
    · nlinarith [Real.sqrt_nonneg s]
    · have : S = 0 := by simp [S, ← hsz]
      rw [this]; exact ht

open RobustOpt2009.Quadratic in
theorem solution {k : ℕ} (y : Fin k → ℝ) (t : ℝ) :
    euclidNorm y ≤ t ↔ (arrow y t).PosSemidef := by
  exact g78r_arrow y t
