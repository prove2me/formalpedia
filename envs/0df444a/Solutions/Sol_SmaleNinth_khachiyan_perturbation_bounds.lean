-- Prove2me | solution 1 for SmaleNinth.khachiyan_perturbation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-06T22:08:51.223258+00:00
-- url     : https://prove2.me/submissions/12a8a72e-f547-4d7e-a27d-ca3df727e03d

import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_SmaleNinth_Khachiyan
import Theorems.Thm_SmaleNinth_khachiyan_feasibility_equiv
import Theorems.Thm_SmaleNinth_khachiyan_volume_lower_bound

open Matrix LinearOptimization

namespace KhachAux

variable {m n : ℕ} {U : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {b : Fin m → ℤ}

lemma box_pos (n U : ℕ) : 0 < SmaleNinth.khachiyanBox n U := by
  unfold SmaleNinth.khachiyanBox
  positivity

/-- Every point of the perturbed-and-boxed polyhedron has sup-norm at most the box radius. -/
lemma abs_le_box {x : Fin n → ℝ}
    (hx : x ∈ polyhedron (SmaleNinth.khachiyanSystemA A) (SmaleNinth.khachiyanSystemb n U b))
    (j : Fin n) : |x j| ≤ SmaleNinth.khachiyanBox n U := by
  have hmem : ∀ i, SmaleNinth.khachiyanSystemb n U b i ≤
      (SmaleNinth.khachiyanSystemA A).mulVec x i := hx
  -- the row `m + j` says `x j ≥ -M`
  have hlow : -(SmaleNinth.khachiyanBox n U) ≤ x j := by
    have hij : (m + (j : ℕ)) < m + n + n := by omega
    have h := hmem ⟨m + (j : ℕ), hij⟩
    have hb : SmaleNinth.khachiyanSystemb n U b ⟨m + (j : ℕ), hij⟩
        = -(SmaleNinth.khachiyanBox n U) := by
      have hnlt : ¬ ((m + (j : ℕ)) < m) := by omega
      simp [SmaleNinth.khachiyanSystemb, dif_neg hnlt]
    have hA : (SmaleNinth.khachiyanSystemA A).mulVec x ⟨m + (j : ℕ), hij⟩ = x j := by
      have harith : (m + (j : ℕ)) - m = (j : ℕ) := by omega
      have hnlt1 : ¬ ((m + (j : ℕ)) < m) := by omega
      have hlt2 : (m + (j : ℕ)) < m + n := by omega
      simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
        dif_neg hnlt1, if_pos hlt2, harith]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have hkj : (k : ℕ) ≠ (j : ℕ) := fun hc => hk (Fin.ext hc)
        simp [hkj]
      · simp
    rw [hb, hA] at h
    exact h
  -- the row `m + n + j` says `-x j ≥ -M`
  have hhigh : x j ≤ SmaleNinth.khachiyanBox n U := by
    have hij : (m + n + (j : ℕ)) < m + n + n := by omega
    have h := hmem ⟨m + n + (j : ℕ), hij⟩
    have hb : SmaleNinth.khachiyanSystemb n U b ⟨m + n + (j : ℕ), hij⟩
        = -(SmaleNinth.khachiyanBox n U) := by
      have hnlt : ¬ ((m + n + (j : ℕ)) < m) := by omega
      simp [SmaleNinth.khachiyanSystemb, dif_neg hnlt]
    have hA : (SmaleNinth.khachiyanSystemA A).mulVec x ⟨m + n + (j : ℕ), hij⟩ = -x j := by
      have harith : (m + n + (j : ℕ)) - m - n = (j : ℕ) := by omega
      have hnlt1 : ¬ ((m + n + (j : ℕ)) < m) := by omega
      have hnlt2 : ¬ ((m + n + (j : ℕ)) < m + n) := by omega
      simp only [Matrix.mulVec, dotProduct, SmaleNinth.khachiyanSystemA,
        dif_neg hnlt1, if_neg hnlt2, harith]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have hkj : (k : ℕ) ≠ (j : ℕ) := fun hc => hk (Fin.ext hc)
        simp [hkj]
      · simp
    rw [hb, hA] at h
    linarith
  rw [abs_le]
  exact ⟨hlow, hhigh⟩


/-- Claim 2: the perturbed-and-boxed polyhedron is bounded. -/
lemma isBounded :
    IsBoundedSet (polyhedron (SmaleNinth.khachiyanSystemA A)
      (SmaleNinth.khachiyanSystemb n U b)) :=
  ⟨SmaleNinth.khachiyanBox n U, fun x hx j => abs_le_box hx j⟩

/-- Claim 3: it is contained in the ball of radius `(n+1)·M`. -/
lemma subset_ball :
    polyhedron (SmaleNinth.khachiyanSystemA A) (SmaleNinth.khachiyanSystemb n U b) ⊆
      ellipsoidBall 0 (SmaleNinth.khachiyanRadius n U) := by
  intro x hx
  have hMpos : 0 < SmaleNinth.khachiyanBox n U := box_pos n U
  have hrpos : 0 < SmaleNinth.khachiyanRadius n U := by
    unfold SmaleNinth.khachiyanRadius
    positivity
  have hinv : ((SmaleNinth.khachiyanRadius n U) ^ 2 •
      (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹
      = ((SmaleNinth.khachiyanRadius n U) ^ 2)⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    field_simp
    simp
  show (x - 0) ⬝ᵥ ((SmaleNinth.khachiyanRadius n U) ^ 2 •
    (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹.mulVec (x - 0) ≤ 1
  rw [hinv]
  simp only [sub_zero]
  have hmv : ((SmaleNinth.khachiyanRadius n U ^ 2)⁻¹ •
      (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x
      = (SmaleNinth.khachiyanRadius n U ^ 2)⁻¹ • x := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [hmv, dotProduct_smul, smul_eq_mul,
    inv_mul_le_iff₀ (by positivity : (0:ℝ) < SmaleNinth.khachiyanRadius n U ^ 2), mul_one]
  -- `x ⬝ᵥ x ≤ n M² ≤ ((n+1)M)²`
  have hsum : x ⬝ᵥ x ≤ (n : ℝ) * SmaleNinth.khachiyanBox n U ^ 2 := by
    have : ∀ j : Fin n, x j * x j ≤ SmaleNinth.khachiyanBox n U ^ 2 := by
      intro j
      have h := abs_le_box (A := A) (b := b) (U := U) hx j
      nlinarith [abs_nonneg (x j), sq_abs (x j), abs_le_box (A := A) (b := b) (U := U) hx j]
    calc x ⬝ᵥ x = ∑ j, x j * x j := rfl
      _ ≤ ∑ _j : Fin n, SmaleNinth.khachiyanBox n U ^ 2 :=
          Finset.sum_le_sum fun j _ => this j
      _ = (n : ℝ) * SmaleNinth.khachiyanBox n U ^ 2 := by
          simp [Finset.sum_const, mul_comm]
  have hgeom : (n : ℝ) * SmaleNinth.khachiyanBox n U ^ 2
      ≤ SmaleNinth.khachiyanRadius n U ^ 2 := by
    unfold SmaleNinth.khachiyanRadius
    have hn1 : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [sq_nonneg (SmaleNinth.khachiyanBox n U), hMpos]
  linarith

end KhachAux

open KhachAux

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ)) :
    ((polyhedron (A.map (Int.cast : ℤ → ℝ))
        (fun i => (b i : ℝ))).Nonempty ↔
      (polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty) ∧
    IsBoundedSet (polyhedron (SmaleNinth.khachiyanSystemA A)
      (SmaleNinth.khachiyanSystemb n U b)) ∧
    polyhedron (SmaleNinth.khachiyanSystemA A) (SmaleNinth.khachiyanSystemb n U b) ⊆
      ellipsoidBall 0 (SmaleNinth.khachiyanRadius n U) ∧
    ((polyhedron (SmaleNinth.khachiyanSystemA A)
        (SmaleNinth.khachiyanSystemb n U b)).Nonempty →
      ENNReal.ofReal (SmaleNinth.khachiyanVolLB n U) ≤
        MeasureTheory.volume
          (polyhedron (SmaleNinth.khachiyanSystemA A)
            (SmaleNinth.khachiyanSystemb n U b))) :=
  ⟨SmaleNinth.khachiyan_feasibility_equiv U hU hn A b hA hb,
   isBounded,
   subset_ball,
   SmaleNinth.khachiyan_volume_lower_bound U hU hn A b hA hb⟩
