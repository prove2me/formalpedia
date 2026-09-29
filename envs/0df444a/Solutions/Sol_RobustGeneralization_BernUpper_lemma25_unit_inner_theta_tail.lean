-- Prove2me | solution 1 for RobustGeneralization.BernUpper.lemma25_unit_inner_theta_tail
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:28:14.463317+00:00
-- url     : https://prove2.me/submissions/f4b156f0-59e1-4ae4-a93e-60520d85b3fd

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

lemma aux_l25_lab_sq (b : Bool) : lab b * lab b = 1 := by
  cases b <;> simp [lab]

lemma aux_l25_abs_lab (b : Bool) : |lab b| = 1 := by
  cases b <;> simp [lab]

lemma aux_l25_norm_pm {d : ℕ} (s : Fin d → Bool) : ‖pm s‖ = Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [pm, Real.norm_eq_abs, aux_l25_abs_lab]

lemma aux_l25_inner_pm {d : ℕ} (s t : Fin d → Bool) :
    inner ℝ (pm s) (pm t) = ∑ i, lab (s i) * lab (t i) := by
  simp [pm, PiLp.inner_apply, mul_comm]

lemma aux_l25_inner_unitZ {d : ℕ} (θ : Fin d → Bool) (p : (Fin d → Bool) × Bool) :
    inner ℝ (unitZ p) (pm θ)
      = (Real.sqrt d)⁻¹ * ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) := by
  have hz : ‖zvec p‖ = Real.sqrt d := by
    rw [zvec, norm_smul, Real.norm_eq_abs, aux_l25_abs_lab, one_mul, aux_l25_norm_pm]
  rw [unitZ, real_inner_smul_left, hz, zvec, real_inner_smul_left, aux_l25_inner_pm,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

lemma aux_l25_event {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (p : (Fin d → Bool) × Bool)
    (h : inner ℝ (unitZ p) (pm θ) ≤ τ * Real.sqrt d) :
    ∑ i, lab p.2 * lab (p.1 i) * lab (θ i) ≤ τ * d := by
  rw [aux_l25_inner_unitZ] at h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by positivity)
    set S := ∑ i, lab p.2 * lab (p.1 i) * lab (θ i)
    have h2 := mul_le_mul_of_nonneg_left h hs.le
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h2
    have h3 : Real.sqrt d * (τ * Real.sqrt d) = τ * d := by
      rw [mul_comm, mul_assoc, hss]
    linarith

lemma aux_l25_scalar (τ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) :
    (1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ ≤ Real.exp (-(3 * τ ^ 2 / 2)) := by
  have habs1 : |τ| ≤ 1 := by rw [abs_of_pos hτ]; linarith
  have habs2 : |-τ| ≤ 1 := by rw [abs_neg, abs_of_pos hτ]; linarith
  have h1 := Real.exp_bound habs1 (n := 5) (by norm_num)
  have h2 := Real.exp_bound habs2 (n := 5) (by norm_num)
  rw [abs_neg] at h2
  rw [abs_of_pos hτ] at h1 h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  norm_num at h1 h2
  rw [abs_le] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have h3 := Real.add_one_le_exp (-(3 * τ ^ 2 / 2))
  have ha : 0 ≤ 1 / 2 + τ := by linarith
  have hb : 0 ≤ 1 / 2 - τ := by linarith
  have hτ5 : τ ^ 5 ≤ τ ^ 4 / 2 := by
    have : τ ^ 5 = τ ^ 4 * τ := by ring
    rw [this]
    have : 0 ≤ τ ^ 4 := by positivity
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2b ha, mul_le_mul_of_nonneg_left h1b hb,
    pow_pos hτ 4, pow_pos hτ 5]

lemma aux_l25_coord (τ : ℝ) (y t : Bool) :
    ∑ b : Bool, (if b = (y == t) then 1 / 2 + τ else 1 / 2 - τ) *
        Real.exp (-τ * (lab y * lab b * lab t))
      = (1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ := by
  cases y <;> cases t <;> simp [lab] <;> ring_nf

lemma aux_l25_mgf {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) :
    ∑ p, bernW θ τ p * Real.exp (-τ * ∑ i, lab p.2 * lab (p.1 i) * lab (θ i))
      = ((1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ) ^ d := by
  rw [Fintype.sum_prod_type_right]
  have key : ∀ y : Bool, ∑ s : Fin d → Bool, bernW θ τ (s, y) *
      Real.exp (-τ * ∑ i, lab (s, y).2 * lab ((s, y).1 i) * lab (θ i))
      = (1 / 2) * ((1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ) ^ d := by
    intro y
    have h1 : ∀ s : Fin d → Bool, bernW θ τ (s, y) *
        Real.exp (-τ * ∑ i, lab (s, y).2 * lab ((s, y).1 i) * lab (θ i))
        = (1 / 2) * ∏ i, ((if s i = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ) *
            Real.exp (-τ * (lab y * lab (s i) * lab (θ i)))) := by
      intro s
      rw [bernW, Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl (fun s _ => h1 s), ← Finset.mul_sum,
      ← Fintype.prod_sum (fun i (b : Bool) => (if b = (y == θ i) then 1 / 2 + τ else 1 / 2 - τ) *
            Real.exp (-τ * (lab y * lab b * lab (θ i))))]
    simp only [aux_l25_coord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun y _ => key y)]
  simp only [Fintype.sum_bool]
  ring

lemma aux_l25_bernW_nonneg {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2)
    (p : (Fin d → Bool) × Bool) : 0 ≤ bernW θ τ p := by
  unfold bernW
  apply mul_nonneg (by norm_num)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

end RobustGeneralization.BernUpper

open RobustGeneralization.BernUpper

theorem solution {d : ℕ} (θ : Fin d → Bool) (τ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2) :
    bprob θ τ (fun p => inner ℝ (unitZ p) (pm θ) ≤ τ * Real.sqrt d)
      ≤ Real.exp (-(τ ^ 2 * d / 2)) := by
  have step1 : bprob θ τ (fun p => inner ℝ (unitZ p) (pm θ) ≤ τ * Real.sqrt d)
      ≤ ∑ p, bernW θ τ p * (Real.exp (τ ^ 2 * d) *
          Real.exp (-τ * ∑ i, lab p.2 * lab (p.1 i) * lab (θ i))) := by
    unfold bprob
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_left _ (aux_l25_bernW_nonneg θ τ hτ hτ' p)
    split_ifs with h
    · rw [← Real.exp_add]
      apply Real.one_le_exp
      have := aux_l25_event θ τ p h
      nlinarith
    · positivity
  have step2 : ∑ p, bernW θ τ p * (Real.exp (τ ^ 2 * d) *
          Real.exp (-τ * ∑ i, lab p.2 * lab (p.1 i) * lab (θ i)))
      = (Real.exp (τ ^ 2) * ((1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ)) ^ d := by
    rw [mul_pow, ← Real.exp_nat_mul, ← aux_l25_mgf θ τ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring_nf
  have hm0 : 0 ≤ (1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ := by
    have ha : 0 ≤ 1 / 2 + τ := by linarith
    have hb : 0 ≤ 1 / 2 - τ := by linarith
    positivity
  have step3 : Real.exp (τ ^ 2) * ((1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ)
      ≤ Real.exp (-(τ ^ 2 / 2)) := by
    calc Real.exp (τ ^ 2) * ((1 / 2 + τ) * Real.exp (-τ) + (1 / 2 - τ) * Real.exp τ)
        ≤ Real.exp (τ ^ 2) * Real.exp (-(3 * τ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (aux_l25_scalar τ hτ hτ') (Real.exp_pos _).le
      _ = Real.exp (-(τ ^ 2 / 2)) := by rw [← Real.exp_add]; ring_nf
  have step4 := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hm0) step3 d
  rw [← Real.exp_nat_mul] at step4
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step4
    _ = _ := by ring_nf
