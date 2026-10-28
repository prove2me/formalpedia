-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_48
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:19:58.483988+00:00
-- url     : https://prove2.me/submissions/41b2bf11-768b-4442-b611-d3b14fd66721

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

open QAOAE3Lin2.Typical QAOAE3Lin2.General Complex in
theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (r : Fin 3) (γ : ℝ)
    (x : QAlgorithms.Qubits n) :
    avgD (fun rhs => Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i r x)) = Real.cos γ ^ QAOAE3Lin2.General.termCount tri i r := by
  classical
  set a : Fin m → ℝ := fun j => spin x (tri j).1 * spin x (tri j).2.1 * spin x (tri j).2.2 *
      spin x (roleBit (tri i) r) with ha
  have hspin : ∀ v, spin x v = 1 ∨ spin x v = -1 := by
    intro v; unfold spin; split_ifs <;> simp
  have hcosa : ∀ j, Real.cos (γ * a j) = Real.cos γ := by
    intro j
    have : a j = 1 ∨ a j = -1 := by
      simp only [ha]
      rcases hspin (tri j).1 with h1 | h1 <;> rcases hspin (tri j).2.1 with h2 | h2 <;>
        rcases hspin (tri j).2.2 with h3 | h3 <;> rcases hspin (roleBit (tri i) r) with h4 | h4 <;>
        simp [h1, h2, h3, h4]
    rcases this with h | h <;> simp [h]
  set S : Fin m → Prop := fun j => sharesOnly tri i j r with hS
  set h : Fin m → Bool → ℂ := fun j b =>
    if S j then exp (((γ * ((if b then -1 else 1) * a j) : ℝ) : ℂ) * I) else 1 with hh
  have hexp : ∀ rhs : Fin m → Bool,
      Real.cos (γ * cPoly tri rhs i r x) = (∏ j, h j (rhs j)).re := by
    intro rhs
    rw [← exp_ofReal_mul_I_re]
    congr 1
    have hcp : cPoly tri rhs i r x = ∑ j, if S j then sgn rhs j * a j else 0 := rfl
    rw [hcp, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : S j
    · have e : γ * (if S j then sgn rhs j * a j else 0) = γ * ((if rhs j then -1 else 1) * a j) := by
        rw [if_pos hj]; rfl
      simp only [hh, hj, if_true]
      rfl
    · simp [hh, hj]
  have hpair : ∀ j, ∑ b : Bool, h j b = if S j then 2 * (Real.cos γ : ℂ) else 2 := by
    intro j
    rw [Fintype.sum_bool]
    by_cases hj : S j
    · have e1 : h j true = exp (((γ * ((-1 : ℝ) * a j) : ℝ) : ℂ) * I) := by
        simp only [hh, if_pos hj, if_true]
      have e2 : h j false = exp (((γ * ((1 : ℝ) * a j) : ℝ) : ℂ) * I) := by
        simp only [hh, if_pos hj]; simp
      have e : exp (((γ * ((-1 : ℝ) * a j) : ℝ) : ℂ) * I) + exp (((γ * ((1 : ℝ) * a j) : ℝ) : ℂ) * I)
          = 2 * Complex.cos ((γ * a j : ℝ) : ℂ) := by
        rw [Complex.cos]
        push_cast
        ring_nf
      rw [e1, e2, e, ← Complex.ofReal_cos, hcosa, if_pos hj]
    · have e1 : h j true = 1 := by simp only [hh, if_neg hj]
      have e2 : h j false = 1 := by simp only [hh, if_neg hj]
      rw [e1, e2, if_neg hj]
      norm_num
  have hsum : ∑ rhs : Fin m → Bool, Real.cos (γ * cPoly tri rhs i r x) =
      (2 : ℝ) ^ m * Real.cos γ ^ termCount tri i r := by
    simp only [hexp]
    rw [← Complex.re_sum, ← Fintype.prod_sum h]
    simp only [hpair]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hc : (Finset.univ.filter S).card = termCount tri i r := rfl
    have hc2 : (Finset.univ.filter fun j => ¬ S j).card = m - termCount tri i r := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
        Fintype.card_fin, hc]
    have hle : termCount tri i r ≤ m := by
      rw [← hc]; exact (Finset.card_filter_le _ _).trans (by simp)
    rw [hc, hc2, mul_pow]
    have : (2 : ℂ) ^ termCount tri i r * 2 ^ (m - termCount tri i r) = 2 ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [show (2 : ℂ) ^ termCount tri i r * (Real.cos γ : ℂ) ^ termCount tri i r *
        2 ^ (m - termCount tri i r) = (((2 : ℝ) ^ m * Real.cos γ ^ termCount tri i r : ℝ) : ℂ) by
      push_cast; rw [← this]; ring]
    rw [Complex.ofReal_re]
  unfold avgD
  rw [hsum]
  field_simp
