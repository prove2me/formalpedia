-- Prove2me | solution 1 for SaglamGV.zeroSumProb_eq_avg_muHat_pow
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-13T15:25:55.859207+00:00
-- url     : https://prove2.me/submissions/371552ba-9daf-48f3-bc98-947dcd74b983

import Definitions.Def_SaglamGV_Fourier
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

private lemma chi_sum {n ℓ : ℕ} (y : Fin n → ZMod 2) (t : Fin ℓ → (Fin n → ZMod 2)) :
    chi y (∑ i, t i) = ∏ i, chi y (t i) := by
  have h (s : Finset (Fin ℓ)) : chi y (∑ i ∈ s, t i) = ∏ i ∈ s, chi y (t i) := by
    induction s using Finset.induction_on with
    | empty => simp [chi, dot]
    | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, chi_add, ih]
  exact h Finset.univ

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

private lemma prod_mu (n d ℓ : ℕ) (t : Fin ℓ → (Fin n → ZMod 2)) :
    (∏ i, mu n d (t i)) =
      if (∀ i, t i ∈ ballP n d) then (1 / (vol n d : ℝ)) ^ ℓ else 0 := by
  classical
  by_cases ht : ∀ i, t i ∈ ballP n d
  · rw [if_pos ht]
    simp [mu, ht]
  · rw [if_neg ht]
    push Not at ht
    obtain ⟨i, hi⟩ := ht
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [mu, hi]

private lemma moment (n d ℓ : ℕ) :
    avgY (fun y ↦ muHat n d y ^ ℓ) = zeroSumProb n d ℓ := by
  classical
  have hexp (y : Fin n → ZMod 2) : muHat n d y ^ ℓ =
      ∑ t : Fin ℓ → (Fin n → ZMod 2), (∏ i, mu n d (t i)) * chi y (∑ i, t i) := by
    calc
      _ = ∑ t : Fin ℓ → (Fin n → ZMod 2), ∏ i, mu n d (t i) * chi y (t i) :=
        Fintype.sum_pow (fun x : Fin n → ZMod 2 ↦ mu n d x * chi y x) ℓ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.prod_mul_distrib, chi_sum]
  calc
    _ = avgY (fun y ↦ ∑ t : Fin ℓ → (Fin n → ZMod 2),
        (∏ i, mu n d (t i)) * chi y (∑ i, t i)) := congrArg avgY (funext hexp)
    _ = ∑ t : Fin ℓ → (Fin n → ZMod 2),
        avgY (fun y ↦ (∏ i, mu n d (t i)) * chi y (∑ i, t i)) := avg_sum _ n _
    _ = ∑ t : Fin ℓ → (Fin n → ZMod 2),
        (∏ i, mu n d (t i)) * (if ∑ i, t i = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [avg_mul, avg_character]
    _ = ∑ t : Fin ℓ → (Fin n → ZMod 2),
        (if (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0 then (1 : ℝ) else 0) *
          ((vol n d : ℝ) ^ ℓ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [prod_mu]
      by_cases ht : ∀ i, t i ∈ ballP n d <;> by_cases hs : ∑ i, t i = 0 <;>
        simp [ht, hs, one_div, inv_pow]
    _ = (∑ t : Fin ℓ → (Fin n → ZMod 2),
        if (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0 then (1 : ℝ) else 0) *
          ((vol n d : ℝ) ^ ℓ)⁻¹ := (Finset.sum_mul ..).symm
    _ = _ := by
      unfold zeroSumProb
      rw [div_eq_mul_inv, Finset.natCast_card_filter]

theorem solution (n d : ℕ) :
    (∀ ℓ : ℕ, zeroSumProb n d ℓ = avgY (fun y ↦ muHat n d y ^ ℓ)) ∧
      avgY (muHat n d) = mu n d 0 ∧ mu n d 0 = 0 := by
  classical
  have hmu0 : mu n d 0 = 0 := by simp [mu, ballP]
  have hp1 : zeroSumProb n d 1 = 0 := by
    have he : (Finset.univ.filter (fun t : Fin 1 → (Fin n → ZMod 2) ↦
        (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨_, hb, hs⟩ := Finset.mem_filter.mp ht
      have hz : t 0 = 0 := by simpa using hs
      have hball := hb 0
      simp [hz, ballP] at hball
    unfold zeroSumProb
    rw [he]
    simp
  refine ⟨fun ℓ ↦ (moment n d ℓ).symm, ?_, hmu0⟩
  have h := moment n d 1
  simpa only [pow_one, hp1, hmu0] using h
