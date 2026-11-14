-- Prove2me | solution 1 for SaglamGV.walkProb_eq
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T15:44:22.214297+00:00
-- url     : https://prove2.me/submissions/4ac93c85-78d0-4f1f-910f-b6e9b158809f

import Theorems.Thm_SaglamGV_zeroSumProb_eq_avg_muHat_pow
import Definitions.Def_SaglamGV_Analytic
set_option autoImplicit false
open Finset SaglamGV

private lemma chi_add {n : ℕ} (y a b : Fin n → ZMod 2) :
    chi y (a + b) = chi y a * chi y b := by
  have hdot : dot (a + b) y = dot a y + dot b y := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  have heps (u v : ZMod 2) :
      (if u + v = 0 then (1 : ℝ) else -1) =
        (if u = 0 then (1 : ℝ) else -1) * (if v = 0 then (1 : ℝ) else -1) := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hcases u with rfl | rfl <;> rcases hcases v with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero]
  unfold chi
  rw [hdot]
  exact heps (dot a y) (dot b y)

private lemma chi_symm {n : ℕ} (x y : Fin n → ZMod 2) : chi x y = chi y x := by
  have hd : dot y x = dot x y := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  unfold chi
  rw [hd]

private lemma chi_add_y {n : ℕ} (a b x : Fin n → ZMod 2) :
    chi (a + b) x = chi a x * chi b x := by
  rw [chi_symm (a + b) x, chi_add, chi_symm x a, chi_symm x b]

private lemma avg_character (n : ℕ) (x : Fin n → ZMod 2) :
    avgY (fun y ↦ chi y x) = if x = 0 then 1 else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    have hcard : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp
    simp [avgY, chi, dot, hcard]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hx (funext hn)
    have hxi : x i = 1 := (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hi
    let e : Fin n → ZMod 2 := Pi.single i 1
    have hce : chi e x = -1 := by simp [chi, dot, e, Pi.single_apply, hxi]
    have hshift := Equiv.sum_comp (Equiv.addRight e) (fun y ↦ chi y x)
    simp only [Equiv.coe_addRight, chi_add_y, hce, mul_neg_one,
      Finset.sum_neg_distrib] at hshift
    have hz : (∑ y, chi y x) = 0 := by linarith
    simp only [avgY, hz, zero_div, if_neg hx]

private lemma avg_sum {α : Type*} (C : Finset α) (n : ℕ)
    (f : α → (Fin n → ZMod 2) → ℝ) :
    avgY (fun y ↦ ∑ x ∈ C, f x y) = ∑ x ∈ C, avgY (f x) := by
  unfold avgY
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_comm

private lemma avg_mul (n : ℕ) (c : ℝ) (f : (Fin n → ZMod 2) → ℝ) :
    avgY (fun y ↦ c * f y) = c * avgY f := by
  unfold avgY
  rw [← Finset.mul_sum]
  ring


private lemma inverse (n : ℕ) (f : (Fin n → ZMod 2) → ℝ) (x : Fin n → ZMod 2) :
    avgY (fun y ↦ fhat f y * chi y x) = f x := by
  classical
  have hneg : -x = x := by ext i; exact CharTwo.neg_eq (x i)
  have hcond (z : Fin n → ZMod 2) : z + x = 0 ↔ z = x := by
    rw [add_eq_zero_iff_eq_neg, hneg]
  calc
    _ = avgY (fun y ↦ ∑ z, f z * chi y (z + x)) := by
      apply congrArg avgY
      funext y
      simp only [fhat, Finset.sum_mul, chi_add, mul_assoc]
    _ = ∑ z, avgY (fun y ↦ f z * chi y (z + x)) := avg_sum _ n _
    _ = ∑ z, f z * (if z + x = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [avg_mul, avg_character]
    _ = f x := by simp [hcond, mul_ite]

private lemma hat_conv (n : ℕ) (f g : (Fin n → ZMod 2) → ℝ) (y : Fin n → ZMod 2) :
    fhat (fun z ↦ ∑ a, f a * g (z - a)) y = fhat f y * fhat g y := by
  classical
  unfold fhat
  calc
    _ = ∑ a, f a * ∑ z, g (z - a) * chi y z := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, Finset.mul_sum]
    _ = ∑ a, (f a * chi y a) * ∑ b, g b * chi y b := by
      apply Finset.sum_congr rfl
      intro a _
      have hs : (∑ z, g (z - a) * chi y z) = (∑ b, g b * chi y b) * chi y a := by
        rw [← Equiv.sum_comp (Equiv.addRight a) (fun z ↦ g (z - a) * chi y z)]
        simp only [Equiv.coe_addRight, add_sub_cancel_right, chi_add, ← mul_assoc,
          Finset.sum_mul]
      rw [hs]
      ring
    _ = _ := (Finset.sum_mul ..).symm

private lemma hat_convPow (n d ℓ : ℕ) (y : Fin (n + 1) → ZMod 2) :
    fhat (convPow n d ℓ) y = fhat (stepLaw n d) y ^ ℓ := by
  classical
  induction ℓ with
  | zero => simp [convPow, fhat, chi, dot]
  | succ ℓ ih =>
      change fhat (fun z ↦ ∑ a, convPow n d ℓ a * stepLaw n d (z - a)) y = _
      rw [hat_conv, ih, pow_succ]

private lemma sum_snoc (n : ℕ) (f : (Fin (n + 1) → ZMod 2) → ℝ) :
    (∑ y, f y) = ∑ b : ZMod 2, ∑ u : Fin n → ZMod 2, f (Fin.snoc u b) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ZMod 2)) f]
  exact Fintype.sum_prod_type _

private lemma sum_two (f : ZMod 2 → ℝ) : (∑ b, f b) = f 0 + f 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  simp

private lemma avg_snoc (n : ℕ) (f : (Fin (n + 1) → ZMod 2) → ℝ) :
    avgY f = (avgY (fun u ↦ f (Fin.snoc u 0)) + avgY (fun u ↦ f (Fin.snoc u 1))) / 2 := by
  unfold avgY
  rw [sum_snoc, sum_two, pow_succ]
  field_simp

private lemma chi_snoc (n : ℕ) (u x : Fin n → ZMod 2) (a b : ZMod 2) :
    chi (Fin.snoc u b) (Fin.snoc x a) = chi u x * (if a * b = 0 then 1 else -1) := by
  have hdot : dot (Fin.snoc x a) (Fin.snoc u b) = dot x u + a * b := by
    simp [dot, Fin.sum_univ_castSucc]
  have heps (v w : ZMod 2) :
      (if v + w = 0 then (1 : ℝ) else -1) =
        (if v = 0 then (1 : ℝ) else -1) * (if w = 0 then (1 : ℝ) else -1) := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hcases v with rfl | rfl <;> rcases hcases w with rfl | rfl <;>
      simp [CharTwo.add_self_eq_zero]
  unfold chi
  rw [hdot]
  exact heps (dot x u) (a * b)

private lemma hat_step (n d : ℕ) (u : Fin n → ZMod 2) (b : ZMod 2) :
    fhat (stepLaw n d) (Fin.snoc u b) = muHat n d u * (if b = 0 then 1 else -1) := by
  classical
  unfold fhat
  rw [sum_snoc, sum_two]
  simp [stepLaw, chi_snoc, muHat, fhat]

private lemma chi_last (n : ℕ) (u : Fin n → ZMod 2) (b : ZMod 2) :
    chi (Fin.snoc u b) (eLast n) = if b = 0 then 1 else -1 := by
  simp [chi, dot, eLast, Pi.single_apply]

private lemma discrete_law (n d ℓ : ℕ) :
    convPow n d ℓ (eLast n) = if Odd ℓ then zeroSumProb n d ℓ else 0 := by
  classical
  calc
    _ = avgY (fun y ↦ fhat (stepLaw n d) y ^ ℓ * chi y (eLast n)) := by
      simp_rw [← hat_convPow]
      exact (inverse (n + 1) (convPow n d ℓ) (eLast n)).symm
    _ = _ := by
      rw [avg_snoc]
      simp_rw [hat_step, chi_last]
      norm_num only [ite_true, one_ne_zero, ite_false, mul_one, mul_neg_one,
        neg_mul, one_pow]
      by_cases hodd : Odd ℓ
      · simp_rw [hodd.neg_pow]
        simp only [neg_neg]
        rw [if_pos hodd]
        have h := (SaglamGV.zeroSumProb_eq_avg_muHat_pow n d).1 ℓ
        rw [← h]
        ring
      · have heven : Even ℓ := Nat.not_odd_iff_even.mp hodd
        simp_rw [heven.neg_pow]
        rw [if_neg hodd]
        simp [avgY, Finset.sum_neg_distrib]
        ring


private lemma exp_series (a : ℝ) :
    HasSum (fun ℓ : ℕ ↦ a ^ ℓ / (ℓ.factorial : ℝ)) (Real.exp a) := by
  simpa only [← Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp a)

private lemma sinh_series (a : ℝ) :
    HasSum (fun ℓ : ℕ ↦ if Odd ℓ then a ^ ℓ / (ℓ.factorial : ℝ) else 0) (Real.sinh a) := by
  have h := ((exp_series a).sub (exp_series (-a))).div_const 2
  rw [Real.sinh_eq]
  convert! h using 1
  funext ℓ
  by_cases ho : Odd ℓ
  · simp only [if_pos ho, ho.neg_pow]
    ring
  · have he : Even ℓ := Nat.not_odd_iff_even.mp ho
    simp [ho, he.neg_pow]

private lemma prob_one (n d : ℕ) : zeroSumProb n d 1 = 0 := by
  have h := SaglamGV.zeroSumProb_eq_avg_muHat_pow n d
  calc
    _ = avgY (muHat n d) := by simpa only [pow_one] using h.1 1
    _ = _ := h.2.1.trans h.2.2

private lemma remove_one (n d : ℕ) (τ : ℝ) (ℓ : ℕ) :
    (if Odd ℓ then τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) =
      (if 3 ≤ ℓ ∧ Odd ℓ then τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) := by
  by_cases ho : Odd ℓ
  · by_cases hℓ : 3 ≤ ℓ
    · simp [ho, hℓ]
    · have he : ℓ = 1 := by obtain ⟨k, hk⟩ := ho; omega
      subst ℓ
      simp [prob_one]
  · simp [ho]

private lemma moment_term (n d : ℕ) (τ : ℝ) (ℓ : ℕ) :
    (if 3 ≤ ℓ ∧ Odd ℓ then τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) =
      avgY (fun y ↦ if Odd ℓ then (τ * muHat n d y) ^ ℓ / (ℓ.factorial : ℝ) else 0) := by
  classical
  rw [← remove_one n d τ ℓ]
  by_cases ho : Odd ℓ
  · rw [if_pos ho]
    calc
      _ = (τ ^ ℓ / (ℓ.factorial : ℝ)) * avgY (fun y ↦ muHat n d y ^ ℓ) := by
        rw [← (SaglamGV.zeroSumProb_eq_avg_muHat_pow n d).1 ℓ]
      _ = _ := by
        rw [← avg_mul]
        apply congrArg avgY
        funext y
        simp only [if_pos ho, mul_pow]
        ring
  · simp [avgY, ho]

private lemma hasSum_average (n : ℕ) (f : ℕ → (Fin n → ZMod 2) → ℝ)
    (a : (Fin n → ZMod 2) → ℝ) (h : ∀ y, HasSum (fun ℓ ↦ f ℓ y) (a y)) :
    HasSum (fun ℓ ↦ avgY (f ℓ)) (avgY a) := by
  classical
  unfold avgY
  exact (hasSum_sum (f := fun y ℓ ↦ f ℓ y) (a := a) (s := Finset.univ)
    (fun y _ ↦ h y)).div_const ((2 : ℝ) ^ n)

private lemma hasSum_moments (n d : ℕ) (τ : ℝ) :
    HasSum (fun ℓ : ℕ ↦ if 3 ≤ ℓ ∧ Odd ℓ then
        τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0)
      (avgY (fun y ↦ Real.sinh (τ * muHat n d y))) := by
  have h := hasSum_average n
    (fun ℓ y ↦ if Odd ℓ then (τ * muHat n d y) ^ ℓ / (ℓ.factorial : ℝ) else 0)
    (fun y ↦ Real.sinh (τ * muHat n d y)) (fun y ↦ sinh_series (τ * muHat n d y))
  exact h.congr_fun (moment_term n d τ)

theorem solution (n d : ℕ) (τ : ℝ) (_hτ : 0 ≤ τ) :
    Real.exp τ * walkProb n d τ (eLast n) =
        ∑' ℓ : ℕ, (if 3 ≤ ℓ ∧ Odd ℓ then
          τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) ∧
      walkProb n d τ (eLast n) =
        Real.exp (-τ) * avgY (fun y ↦ Real.sinh (τ * muHat n d y)) ∧
      walkProb n d τ (eLast n) =
        Real.exp (-τ) * avgY (fun y ↦ sMinus (τ * muHat n d y)) := by
  classical
  let g := fun ℓ : ℕ ↦ if 3 ≤ ℓ ∧ Odd ℓ then
    τ ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0
  have hs := hasSum_moments n d τ
  have hterm (ℓ : ℕ) :
      Real.exp (-τ) * τ ^ ℓ / (ℓ.factorial : ℝ) * convPow n d ℓ (eLast n) =
        Real.exp (-τ) * g ℓ := by
    dsimp [g]
    rw [discrete_law, ← remove_one n d τ ℓ]
    by_cases ho : Odd ℓ
    · simp only [if_pos ho]
      ring
    · simp [ho]
  have hw : walkProb n d τ (eLast n) =
      Real.exp (-τ) * avgY (fun y ↦ Real.sinh (τ * muHat n d y)) := by
    calc
      _ = ∑' ℓ : ℕ, Real.exp (-τ) * g ℓ := tsum_congr hterm
      _ = Real.exp (-τ) * ∑' ℓ : ℕ, g ℓ := tsum_mul_left
      _ = _ := by rw [hs.tsum_eq]
  have hz : avgY (fun y ↦ τ * muHat n d y) = 0 := by
    rw [avg_mul, (SaglamGV.zeroSumProb_eq_avg_muHat_pow n d).2.1,
      (SaglamGV.zeroSumProb_eq_avg_muHat_pow n d).2.2, mul_zero]
  have hsm : avgY (fun y ↦ sMinus (τ * muHat n d y)) =
      avgY (fun y ↦ Real.sinh (τ * muHat n d y)) := by
    calc
      _ = avgY (fun y ↦ Real.sinh (τ * muHat n d y)) -
          avgY (fun y ↦ τ * muHat n d y) := by
        unfold sMinus avgY
        rw [Finset.sum_sub_distrib, sub_div]
      _ = _ := by rw [hz, sub_zero]
  refine ⟨?_, hw, ?_⟩
  · rw [hw, ← mul_assoc, ← Real.exp_add]
    simpa using hs.tsum_eq.symm
  · rw [hsm]
    exact hw
