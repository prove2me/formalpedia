-- Prove2me | solution 1 for OnlineCombOpt.Exp2Full.theorem_1_full_domain
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:40:53.243199+00:00
-- url     : https://prove2.me/submissions/c72a341a-5000-4466-8d81-e507624d61a9

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset
open OnlineCombOpt.Exp2LB

namespace Exp2FullProof
noncomputable section

def bitReal (b : Bool) : ℝ := if b then 1 else 0

/-- Coordinate layout: `P` small pairs, two intervals of length `b`, `R` unused coordinates. -/
abbrev Lay (P b R : ℕ) : Type := (Fin P ⊕ Fin P) ⊕ ((Fin b ⊕ Fin b) ⊕ Fin R)

def layG (P b R : ℕ) (s : Fin (P + 1) → Bool) : Lay P b R → ℝ
  | Sum.inl (Sum.inl j) => 1 - bitReal (s j.castSucc)
  | Sum.inl (Sum.inr j) => bitReal (s j.castSucc)
  | Sum.inr (Sum.inl (Sum.inl _)) => 1 - bitReal (s (Fin.last P))
  | Sum.inr (Sum.inl (Sum.inr _)) => bitReal (s (Fin.last P))
  | Sum.inr (Sum.inr _) => 0

def smallL (P b R : ℕ) (ε : ℝ) : Lay P b R → ℝ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => ε
  | Sum.inr (Sum.inl (Sum.inl _)) => 0
  | Sum.inr (Sum.inl (Sum.inr _)) => ε / b
  | Sum.inr (Sum.inr _) => 0

def altL (P b R : ℕ) (n t : ℕ) : Lay P b R → ℝ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr (Sum.inl (Sum.inl _)) => if t < 2 * (n / 2) ∧ Even t then 1 else 0
  | Sum.inr (Sum.inl (Sum.inr _)) => if t < 2 * (n / 2) ∧ Odd t then 1 else 0
  | Sum.inr (Sum.inr _) => 0

variable {P b R d : ℕ}

def act (e : Lay P b R ≃ Fin d) (s : Fin (P + 1) → Bool) : Fin d → ℝ :=
  fun i => layG P b R s (e.symm i)

def actSet (e : Lay P b R ≃ Fin d) : Finset (Fin d → ℝ) :=
  Finset.univ.image (act e)

def smallZ (e : Lay P b R ≃ Fin d) (ε : ℝ) : ℕ → Fin d → ℝ :=
  fun _ i => smallL P b R ε (e.symm i)

def altZ (e : Lay P b R ≃ Fin d) (n : ℕ) : ℕ → Fin d → ℝ :=
  fun t i => altL P b R n t (e.symm i)

theorem dot_lay (e : Lay P b R ≃ Fin d) (s : Fin (P + 1) → Bool) (F : Lay P b R → ℝ) :
    act e s ⬝ᵥ (fun i => F (e.symm i)) = ∑ x, layG P b R s x * F x := by
  unfold dotProduct act
  exact e.symm.sum_comp (fun x => layG P b R s x * F x)

theorem act_injective (e : Lay P b R ≃ Fin d) (hb : 0 < b) :
    Function.Injective (act e) := by
  intro s s' h
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hh := congrFun h (e (Sum.inr (Sum.inl (Sum.inr ⟨0, hb⟩))))
    simp only [act, Equiv.symm_apply_apply, layG] at hh
    unfold bitReal at hh
    cases h1 : s (Fin.last P) <;> cases h2 : s' (Fin.last P) <;> simp_all
  · have hh := congrFun h (e (Sum.inl (Sum.inr i)))
    simp only [act, Equiv.symm_apply_apply, layG] at hh
    unfold bitReal at hh
    cases h1 : s i.castSucc <;> cases h2 : s' i.castSucc <;> simp_all

theorem binary_actions (e : Lay P b R ≃ Fin d) : IsBinaryActionSet (actSet e) (P + b) := by
  classical
  constructor
  · exact ⟨act e (fun _ => false), mem_image.mpr ⟨_, mem_univ _, rfl⟩⟩
  intro a ha
  obtain ⟨s, _, rfl⟩ := mem_image.mp ha
  constructor
  · intro i
    simp only [act]
    rcases e.symm i with ((j | j) | ((j | j) | j)) <;> simp only [layG, bitReal] <;>
      (try split_ifs) <;> norm_num
  · have h1 : ∑ i, act e s i = ∑ x, layG P b R s x := by
      unfold act
      exact e.symm.sum_comp (fun x => layG P b R s x)
    rw [h1]
    simp only [Fintype.sum_sum_type, layG, Finset.sum_sub_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

theorem sum_actions (e : Lay P b R ≃ Fin d) (hb : 0 < b) (F : (Fin d → ℝ) → ℝ) :
    ∑ a ∈ actSet e, F a = ∑ s : Fin (P + 1) → Bool, F (act e s) := by
  classical
  exact sum_image (fun a _ c _ hac => act_injective e hb hac)

theorem small_dot (e : Lay P b R ≃ Fin d) (hb : 0 < b) (s : Fin (P + 1) → Bool) (ε : ℝ)
    (t : ℕ) : act e s ⬝ᵥ smallZ e ε t = ∑ j, ε * bitReal (s j) := by
  have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold smallZ
  rw [dot_lay, Fin.sum_univ_castSucc]
  simp only [Fintype.sum_sum_type, layG, smallL, mul_zero, sum_const_zero, zero_add,
    add_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring_nf
  simp [mul_comm]

theorem alt_dot_even (e : Lay P b R ≃ Fin d) (s : Fin (P + 1) → Bool) (n j : ℕ)
    (hj : j < n / 2) :
    act e s ⬝ᵥ altZ e n (2 * j) = (b : ℝ) * (1 - bitReal (s (Fin.last P))) := by
  have he : Even (2 * j) := ⟨j, by omega⟩
  have ho : ¬ Odd (2 * j) := by rintro ⟨u, hu⟩; omega
  have ht : 2 * j < 2 * (n / 2) := by omega
  unfold altZ
  rw [dot_lay]
  simp [Fintype.sum_sum_type, layG, altL, he, ho, ht]
  ring

theorem alt_dot_odd (e : Lay P b R ≃ Fin d) (s : Fin (P + 1) → Bool) (n j : ℕ)
    (hj : j < n / 2) :
    act e s ⬝ᵥ altZ e n (2 * j + 1) = (b : ℝ) * bitReal (s (Fin.last P)) := by
  have ho : Odd (2 * j + 1) := ⟨j, by omega⟩
  have he : ¬ Even (2 * j + 1) := by rintro ⟨u, hu⟩; omega
  have ht : 2 * j + 1 < 2 * (n / 2) := by omega
  unfold altZ
  rw [dot_lay]
  simp [Fintype.sum_sum_type, layG, altL, he, ho, ht]

theorem alt_dot_after (e : Lay P b R ≃ Fin d) (n t : ℕ) (ht : 2 * (n / 2) ≤ t)
    (a : Fin d → ℝ) : a ⬝ᵥ altZ e n t = 0 := by
  have h : ¬ t < 2 * (n / 2) := not_lt.mpr ht
  unfold dotProduct altZ
  apply sum_eq_zero
  intro i _
  rcases e.symm i with ((j | j) | ((j | j) | j)) <;> simp [altL, h]

end
end Exp2FullProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2FullProof
noncomputable section

theorem partition_pos {d : ℕ} (A : Finset (Fin d → ℝ)) (hA : A.Nonempty)
    (eta : ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    0 < ∑ a ∈ A, Real.exp (-eta * cumLoss a z t) :=
  sum_pos (fun _ _ => Real.exp_pos _) hA

theorem cumLoss_succ {d : ℕ} (a : Fin d → ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    cumLoss a z (t + 1) = cumLoss a z t + a ⬝ᵥ z t := by
  simp [cumLoss, sum_range_succ]

theorem gibbs_weights {d : ℕ} (A : Finset (Fin d → ℝ)) (hA : A.Nonempty)
    (eta : ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) (a : Fin d → ℝ) (ha : a ∈ A) :
    exp2Weights A eta z t a = Real.exp (-eta * cumLoss a z t) /
      (∑ b ∈ A, Real.exp (-eta * cumLoss b z t)) := by
  classical
  induction t generalizing a with
  | zero => simp [exp2Weights, ha, cumLoss]
  | succ t ih =>
    have hs : ∀ b ∈ A, Real.exp (-eta * (b ⬝ᵥ z t)) * exp2Weights A eta z t b =
        Real.exp (-eta * cumLoss b z (t + 1)) /
          (∑ c ∈ A, Real.exp (-eta * cumLoss c z t)) := by
      intro b hb
      rw [ih b hb, ← mul_div_assoc, ← Real.exp_add]
      congr 2
      rw [cumLoss_succ]
      ring
    rw [exp2Weights, hs a ha]
    have he := sum_congr rfl hs
    rw [he, ← sum_div]
    have hp := (partition_pos A hA eta z t).ne'
    have hq := (partition_pos A hA eta z (t + 1)).ne'
    field_simp

def bitProb (eta c : ℝ) (b : Bool) : ℝ :=
  Real.exp (-eta * c * bitReal b) / (1 + Real.exp (-eta * c))

theorem bitProb_sum (eta c : ℝ) : ∑ b : Bool, bitProb eta c b = 1 := by
  have hp : 0 < 1 + Real.exp (-eta * c) := by positivity
  simp [bitProb, bitReal]
  field_simp
  ring

theorem bitProb_true (eta c : ℝ) : bitProb eta c true = 1 / (1 + Real.exp (eta * c)) := by
  have hp : 0 < Real.exp (eta * c) := Real.exp_pos _
  have hq : 0 < 1 + Real.exp (eta * c) := by positivity
  simp only [bitProb, bitReal, if_true, mul_one]
  rw [show -eta * c = -(eta * c) by ring, Real.exp_neg]
  field_simp
  ring

theorem product_probability_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (eta : ℝ)
    (c : ι → ℝ) : ∑ b : ι → Bool, ∏ j, bitProb eta (c j) (b j) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [bitProb_sum, prod_const_one]

theorem product_probability_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (eta : ℝ)
    (c : ι → ℝ) (j : ι) :
    ∑ b : ι → Bool, (∏ i, bitProb eta (c i) (b i)) * bitReal (b j) =
      1 / (1 + Real.exp (eta * c j)) := by
  classical
  calc
    _ = ∑ b : ι → Bool, ∏ i, (bitProb eta (c i) (b i) *
        if i = j then bitReal (b i) else 1) := by
      apply sum_congr rfl
      intro b _
      simp only [prod_mul_distrib, prod_ite_eq', mem_univ, if_true]
    _ = ∏ i, ∑ b : Bool, (bitProb eta (c i) b * if i = j then bitReal b else 1) :=
      (Fintype.prod_sum (fun i (b : Bool) =>
        bitProb eta (c i) b * if i = j then bitReal b else 1)).symm
    _ = ∏ i, if i = j then bitProb eta (c j) true else 1 := by
      apply prod_congr rfl
      intro i _
      by_cases h : i = j
      · subst i
        simp [bitReal]
      · simp only [if_neg h, mul_one]
        exact bitProb_sum eta (c i)
    _ = bitProb eta (c j) true := by simp
    _ = _ := bitProb_true eta (c j)

theorem exponential_product {ι : Type*} [Fintype ι]
    (eta c0 : ℝ) (c : ι → ℝ) (b : ι → Bool) :
    Real.exp (-eta * (c0 + ∑ j, c j * bitReal (b j))) =
      Real.exp (-eta * c0) * ∏ j, Real.exp (-eta * c j * bitReal (b j)) := by
  rw [mul_add, Real.exp_add, mul_sum, Real.exp_sum]
  congr 1
  apply prod_congr rfl
  intro j _
  congr 1
  ring

theorem normalized_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eta c0 : ℝ) (c : ι → ℝ) (b : ι → Bool) :
    Real.exp (-eta * (c0 + ∑ j, c j * bitReal (b j))) /
      (∑ a : ι → Bool, Real.exp (-eta * (c0 + ∑ j, c j * bitReal (a j)))) =
        ∏ j, bitProb eta (c j) (b j) := by
  simp_rw [exponential_product]
  rw [← mul_sum, ← Fintype.prod_sum (fun j (b : Bool) =>
    Real.exp (-eta * c j * bitReal b))]
  have hz : ∀ j : ι, (∑ b : Bool, Real.exp (-eta * c j * bitReal b)) =
      1 + Real.exp (-eta * c j) := by
    intro j
    simp [bitReal, add_comm]
  simp_rw [hz]
  rw [mul_div_mul_left _ _ (Real.exp_pos _).ne']
  exact (Finset.prod_div_distrib _ _).symm

variable {P b R d : ℕ}

theorem step_mean (e : Lay P b R ≃ Fin d) (hb : 0 < b) (eta : ℝ)
    (z : ℕ → Fin d → ℝ) (t : ℕ) (c0 : ℝ) (c : Fin (P + 1) → ℝ)
    (r0 : ℝ) (r : Fin (P + 1) → ℝ)
    (hc : ∀ s, cumLoss (act e s) z t = c0 + ∑ j, c j * bitReal (s j))
    (hr : ∀ s, act e s ⬝ᵥ z t = r0 + ∑ j, r j * bitReal (s j)) :
    ∑ a ∈ actSet e, exp2Weights (actSet e) eta z t a * (a ⬝ᵥ z t) =
      r0 + ∑ j, r j / (1 + Real.exp (eta * c j)) := by
  classical
  have hA := (binary_actions e).1
  have hw : ∀ s, exp2Weights (actSet e) eta z t (act e s) =
      ∏ j, bitProb eta (c j) (s j) := by
    intro s
    rw [gibbs_weights _ hA _ _ _ _ (mem_image.mpr ⟨s, mem_univ _, rfl⟩),
      sum_actions e hb]
    simp_rw [hc]
    exact normalized_product eta c0 c s
  rw [sum_actions e hb]
  simp_rw [hw, hr, mul_add, mul_sum]
  rw [sum_add_distrib, ← sum_mul, product_probability_sum, one_mul, sum_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  simp_rw [show ∀ s : Fin (P + 1) → Bool,
    (∏ i, bitProb eta (c i) (s i)) * (r j * bitReal (s j)) =
      r j * ((∏ i, bitProb eta (c i) (s i)) * bitReal (s j)) by intro s; ring]
  rw [← mul_sum, product_probability_mean]
  ring

/-! ### The constant adversary -/

theorem small_cum (e : Lay P b R ≃ Fin d) (hb : 0 < b) (s : Fin (P + 1) → Bool) (ε : ℝ)
    (t : ℕ) :
    cumLoss (act e s) (smallZ e ε) t = ∑ j, ((t : ℝ) * ε) * bitReal (s j) := by
  simp only [cumLoss, small_dot e hb, sum_const, card_range, nsmul_eq_mul, Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem small_mean (e : Lay P b R ≃ Fin d) (hb : 0 < b) (t : ℕ) (η ε : ℝ) :
    ∑ a ∈ actSet e, exp2Weights (actSet e) η (smallZ e ε) t a * (a ⬝ᵥ smallZ e ε t) =
      ((P : ℝ) + 1) * (ε / (1 + Real.exp (η * ((t : ℝ) * ε)))) := by
  have hc : ∀ s, cumLoss (act e s) (smallZ e ε) t =
      0 + ∑ j, (fun _ => (t : ℝ) * ε) j * bitReal (s j) := by
    intro s
    rw [zero_add, small_cum e hb]
  have hr : ∀ s, act e s ⬝ᵥ smallZ e ε t = 0 + ∑ j, (fun _ => ε) j * bitReal (s j) := by
    intro s
    rw [zero_add, small_dot e hb]
  rw [step_mean e hb η (smallZ e ε) t 0 _ 0 _ hc hr]
  simp only [zero_add, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem small_regret (e : Lay P b R ≃ Fin d) (hb : 0 < b) (n : ℕ) (η ε : ℝ) (he : 0 ≤ ε) :
    exp2Regret (actSet e) η (smallZ e ε) n =
      ∑ t ∈ Finset.range n, ((P : ℝ) + 1) * (ε / (1 + Real.exp (η * ((t : ℝ) * ε)))) := by
  classical
  have hA := (binary_actions e).1
  have hmin : (actSet e).inf' hA (fun a => cumLoss a (smallZ e ε) n) = 0 := by
    apply le_antisymm
    · have hm : act e (fun _ => false) ∈ actSet e :=
        mem_image_of_mem _ (mem_univ _)
      calc
        _ ≤ cumLoss (act e (fun _ => false)) (smallZ e ε) n :=
          Finset.inf'_le (fun a => cumLoss a (smallZ e ε) n) hm
        _ = 0 := by simp [small_cum e hb, bitReal]
    · apply Finset.le_inf'
      intro a ha
      obtain ⟨s, _, rfl⟩ := mem_image.mp ha
      rw [small_cum e hb]
      apply sum_nonneg
      intro j _
      apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he)
      simp only [bitReal]
      split_ifs <;> norm_num
  simp only [exp2Regret, dif_pos hA, hmin, sub_zero, exp2ExpectedLoss, small_mean e hb]

theorem small_losses_mem (e : Lay P b R ≃ Fin d) (hb : 0 < b) (ε : ℝ) (he : 0 ≤ ε)
    (he1 : ε ≤ 1) : ∀ t i, smallZ e ε t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t i
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : 0 ≤ ε / b := div_nonneg he (by positivity)
  have h2 : ε / b ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  simp only [smallZ]
  rcases e.symm i with ((j | j) | ((j | j) | j)) <;> simp only [smallL] <;>
    first | exact ⟨le_refl _, zero_le_one⟩ | exact ⟨he, he1⟩ | exact ⟨h1, h2⟩

theorem small_regret_lower (e : Lay P b R ≃ Fin d) (hb : 0 < b) (n : ℕ) (η ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hcut : η * (n : ℝ) * ε ≤ 1) :
    (n : ℝ) * ((P : ℝ) + 1) * ε / 4 ≤ exp2Regret (actSet e) η (smallZ e ε) n := by
  rw [small_regret e hb n η ε hε]
  calc
    (n : ℝ) * ((P : ℝ) + 1) * ε / 4 = ∑ _t ∈ Finset.range n, ((P : ℝ) + 1) * ε / 4 := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ ∑ t ∈ Finset.range n, ((P : ℝ) + 1) * (ε / (1 + Real.exp (η * ((t : ℝ) * ε)))) := by
      apply Finset.sum_le_sum
      intro t ht
      have htn : (t : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt (mem_range.mp ht))
      have hz : η * ((t : ℝ) * ε) ≤ 1 := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htn hη) hε
        nlinarith
      have he : Real.exp (η * ((t : ℝ) * ε)) ≤ 3 :=
        (Real.exp_le_exp.mpr hz).trans Real.exp_one_lt_three.le
      have hpos : 0 < 1 + Real.exp (η * ((t : ℝ) * ε)) := by positivity
      rw [mul_div_assoc', div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hpos]
      have hP : 0 ≤ ((P : ℝ) + 1) * ε := by positivity
      nlinarith [mul_nonneg hP (show 0 ≤ 3 - Real.exp (η * ((t : ℝ) * ε)) by linarith)]

/-! ### The alternating adversary -/

theorem alt_cum_even (e : Lay P b R ≃ Fin d) (n : ℕ) (s : Fin (P + 1) → Bool)
    (j : ℕ) (hj : j ≤ n / 2) :
    cumLoss (act e s) (altZ e n) (2 * j) = (j : ℝ) * b := by
  induction j with
  | zero => simp [cumLoss]
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, cumLoss_succ,
      cumLoss_succ, ih (by omega), alt_dot_even e s n j (by omega),
      alt_dot_odd e s n j (by omega)]
    push_cast
    ring

theorem alt_cum_odd (e : Lay P b R ≃ Fin d) (n : ℕ) (s : Fin (P + 1) → Bool)
    (j : ℕ) (hj : j < n / 2) :
    cumLoss (act e s) (altZ e n) (2 * j + 1) =
      ((j : ℝ) + 1) * b - b * bitReal (s (Fin.last P)) := by
  rw [cumLoss_succ, alt_cum_even e n s j (by omega), alt_dot_even e s n j hj]
  ring

theorem loss_cum_eq_of_after {d : ℕ} (a : Fin d → ℝ) (z : ℕ → Fin d → ℝ)
    (m n : ℕ) (hmn : m ≤ n) (hz : ∀ t, m ≤ t → a ⬝ᵥ z t = 0) :
    cumLoss a z n = cumLoss a z m := by
  symm
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro t _ htm
  exact hz t (by simpa only [mem_range, not_lt] using htm)

theorem alt_cum_horizon (e : Lay P b R ≃ Fin d) (n : ℕ) (s : Fin (P + 1) → Bool) :
    cumLoss (act e s) (altZ e n) n = ((n / 2 : ℕ) : ℝ) * b := by
  rw [loss_cum_eq_of_after (act e s) (altZ e n)
    (2 * (n / 2)) n (by omega) (fun t ht => alt_dot_after e n t ht _)]
  exact alt_cum_even e n s (n / 2) le_rfl

def lastCoeff (P : ℕ) (x : ℝ) (j : Fin (P + 1)) : ℝ :=
  if j = Fin.last P then x else 0

theorem lastCoeff_sum (P : ℕ) (x : ℝ) (f : Fin (P + 1) → ℝ) :
    ∑ j, lastCoeff P x j * f j = x * f (Fin.last P) := by
  simp [lastCoeff]

theorem alt_mean_even (e : Lay P b R ≃ Fin d) (hb : 0 < b) (n j : ℕ)
    (hj : j < n / 2) (η : ℝ) :
    ∑ a ∈ actSet e, exp2Weights (actSet e) η (altZ e n) (2 * j) a *
      (a ⬝ᵥ altZ e n (2 * j)) = (b : ℝ) / 2 := by
  have hc : ∀ s, cumLoss (act e s) (altZ e n) (2 * j) =
      (j : ℝ) * b + ∑ l, (0 : ℝ) * bitReal (s l) := by
    intro s
    simpa using alt_cum_even e n s j (by omega)
  have hr : ∀ s, act e s ⬝ᵥ altZ e n (2 * j) =
      (b : ℝ) + ∑ l, lastCoeff P (-(b : ℝ)) l * bitReal (s l) := by
    intro s
    rw [lastCoeff_sum, alt_dot_even e s n j hj]
    ring
  have h := step_mean e hb η (altZ e n) (2 * j)
    ((j : ℝ) * b) (fun _ => 0) b (lastCoeff P (-(b : ℝ))) hc hr
  calc
    _ = (b : ℝ) + (-(b : ℝ)) / 2 := by
      simpa [lastCoeff, ite_div, show (1 : ℝ) + 1 = 2 by norm_num] using h
    _ = _ := by ring

theorem alt_mean_odd (e : Lay P b R ≃ Fin d) (hb : 0 < b) (n j : ℕ)
    (hj : j < n / 2) (η : ℝ) :
    ∑ a ∈ actSet e, exp2Weights (actSet e) η (altZ e n) (2 * j + 1) a *
      (a ⬝ᵥ altZ e n (2 * j + 1)) =
        (b : ℝ) * Real.exp (η * b) / (1 + Real.exp (η * b)) := by
  have hc : ∀ s, cumLoss (act e s) (altZ e n) (2 * j + 1) =
      ((j : ℝ) + 1) * b + ∑ l, lastCoeff P (-(b : ℝ)) l * bitReal (s l) := by
    intro s
    rw [lastCoeff_sum, alt_cum_odd e n s j hj]
    ring
  have hr : ∀ s, act e s ⬝ᵥ altZ e n (2 * j + 1) =
      0 + ∑ l, lastCoeff P (b : ℝ) l * bitReal (s l) := by
    intro s
    rw [lastCoeff_sum, zero_add, alt_dot_odd e s n j hj]
  have h := step_mean e hb η (altZ e n) (2 * j + 1)
    (((j : ℝ) + 1) * b) (lastCoeff P (-(b : ℝ))) 0 (lastCoeff P b) hc hr
  have h' : (∑ a ∈ actSet e, exp2Weights (actSet e) η (altZ e n)
      (2 * j + 1) a * (a ⬝ᵥ altZ e n (2 * j + 1))) =
      (b : ℝ) / (1 + Real.exp (-(η * b))) := by
    have ht : ∀ l, lastCoeff P (b : ℝ) l /
        (1 + Real.exp (η * lastCoeff P (-(b : ℝ)) l)) =
        if l = Fin.last P then (b : ℝ) / (1 + Real.exp (-(η * b))) else 0 := by
      intro l
      by_cases hl : l = Fin.last P <;> simp [lastCoeff, hl]
    simpa only [ht, sum_ite_eq', mem_univ, if_true, zero_add] using h
  rw [h', Real.exp_neg]
  have he := Real.exp_pos (η * b)
  field_simp
  ring

theorem alt_expected_pairs (e : Lay P b R ≃ Fin d) (hb : 0 < b) (n j : ℕ)
    (hj : j ≤ n / 2) (η : ℝ) :
    exp2ExpectedLoss (actSet e) η (altZ e n) (2 * j) =
      (j : ℝ) * ((b : ℝ) / 2 + b * Real.exp (η * b) / (1 + Real.exp (η * b))) := by
  induction j with
  | zero => simp [exp2ExpectedLoss]
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega]
    simp only [exp2ExpectedLoss, sum_range_succ]
    rw [← exp2ExpectedLoss, ih (by omega), alt_mean_even e hb n j (by omega),
      alt_mean_odd e hb n j (by omega)]
    push_cast
    ring

theorem alt_regret (e : Lay P b R ≃ Fin d) (hb : 0 < b) (n : ℕ) (η : ℝ) :
    exp2Regret (actSet e) η (altZ e n) n =
      ((n / 2 : ℕ) : ℝ) * b *
        (Real.exp (η * b) / (1 + Real.exp (η * b)) - (1 / 2 : ℝ)) := by
  classical
  have hA := (binary_actions e).1
  have hc : ∀ a ∈ actSet e, cumLoss a (altZ e n) n = ((n / 2 : ℕ) : ℝ) * b := by
    intro a ha
    obtain ⟨s, _, rfl⟩ := mem_image.mp ha
    exact alt_cum_horizon e n s
  have hmin : (actSet e).inf' hA (fun a => cumLoss a (altZ e n) n) =
      ((n / 2 : ℕ) : ℝ) * b := by
    apply le_antisymm
    · obtain ⟨a, ha⟩ := hA
      simpa only [hc a ha] using Finset.inf'_le (fun a => cumLoss a (altZ e n) n) ha
    · exact Finset.le_inf' hA _ (fun a ha => (hc a ha).ge)
  have he : exp2ExpectedLoss (actSet e) η (altZ e n) n =
      exp2ExpectedLoss (actSet e) η (altZ e n) (2 * (n / 2)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (show 2 * (n / 2) ≤ n by omega))
    intro t _ ht
    have ht' : 2 * (n / 2) ≤ t := by simpa only [mem_range, not_lt] using ht
    simp only [alt_dot_after e n t ht', mul_zero, sum_const_zero]
  rw [exp2Regret, dif_pos hA, hmin, he, alt_expected_pairs e hb n (n / 2) le_rfl]
  ring

theorem alt_losses_mem (e : Lay P b R ≃ Fin d) (n : ℕ) :
    ∀ t i, altZ e n t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t i
  simp only [altZ]
  rcases e.symm i with ((j | j) | ((j | j) | j)) <;> simp only [altL] <;>
    (try split_ifs) <;> norm_num

end
end Exp2FullProof

namespace Exp2FullProof
noncomputable section

theorem logistic_lower (x : ℝ) (hx : 0 ≤ x) :
    x / (2 * (x + 2)) ≤ Real.exp x / (1 + Real.exp x) - (1 / 2 : ℝ) := by
  have hE : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hpos : 0 < 1 + Real.exp x := by positivity
  have key : Real.exp x / (1 + Real.exp x) - 1 / 2 =
      (Real.exp x - 1) / (2 * (1 + Real.exp x)) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The parameter arithmetic: `(i)`, `(ii)`, `(iii)` for `P = q`, `b = 2q + r`. -/
theorem param_ineq (d : ℕ) (hd : 2 ≤ d) :
    12 * d ≤ 100 * (2 * (d / 2 / 3) + d / 2 % 3) ∧
    16 * d ≤ 100 * (d / 2 / 3 + 1) ∧
    128 * d ^ 3 ≤ 10000 * (d / 2 / 3 + 1) * (2 * (d / 2 / 3) + d / 2 % 3) ^ 2 := by
  set q := d / 2 / 3 with hq
  set r := d / 2 % 3 with hr
  have hdq : d ≤ 6 * q + 2 * r + 1 := by omega
  have hr3 : r < 3 := by omega
  have hqr : 1 ≤ 3 * q + r := by omega
  refine ⟨by omega, by omega, ?_⟩
  have h3 : d ^ 3 ≤ (6 * q + 2 * r + 1) ^ 3 := Nat.pow_le_pow_left hdq 3
  have key : 128 * (6 * q + 2 * r + 1) ^ 3 ≤ 10000 * (q + 1) * (2 * q + r) ^ 2 := by
    interval_cases r
    · have hq1 : 1 ≤ q := by omega
      nlinarith [Nat.mul_le_mul hq1 hq1, Nat.mul_le_mul (Nat.mul_le_mul hq1 hq1) hq1]
    · nlinarith [Nat.zero_le q, Nat.zero_le (q * q), Nat.zero_le (q * q * q)]
    · nlinarith [Nat.zero_le q, Nat.zero_le (q * q), Nat.zero_le (q * q * q)]
  calc 128 * d ^ 3 ≤ 128 * (6 * q + 2 * r + 1) ^ 3 := Nat.mul_le_mul_left _ h3
    _ ≤ _ := key

/-- The case analysis over the learning rate. -/
theorem final_ineq (n d b P N2 η : ℝ) (hd : 2 ≤ d) (hdn : d ≤ n) (hb : 1 ≤ b) (hP : 0 ≤ P)
    (hN2 : n ≤ 3 * N2) (h1 : 12 * d ≤ 100 * b) (h2 : 16 * d ≤ 100 * (P + 1))
    (h3 : 128 * d ^ 3 ≤ 10000 * (P + 1) * b ^ 2) (hη : 0 ≤ η) :
    (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤
        N2 * b * (Real.exp (η * b) / (1 + Real.exp (η * b)) - (1 / 2 : ℝ)) ∨
      (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤
        n * (P + 1) * (1 / (1 + η * n)) / 4 := by
  have hn : 0 < n := by linarith
  set S := Real.sqrt d * Real.sqrt n with hS
  have hS0 : 0 ≤ S := by positivity
  have hS2 : S ^ 2 = d * n := by
    rw [hS, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hn.le]
  have hSn : S ≤ n := by
    have : S ^ 2 ≤ n ^ 2 := by rw [hS2]; nlinarith
    nlinarith
  have hT : (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n = d * S / 100 := by
    rw [hS]; ring
  rw [hT]
  have hTle : d * S / 100 ≤ d * n / 100 := by
    have := mul_le_mul_of_nonneg_left hSn (show 0 ≤ d by linarith)
    linarith
  set x := η * b with hx
  have hx0 : 0 ≤ x := by positivity
  have hg := logistic_lower x hx0
  set g := Real.exp x / (1 + Real.exp x) - (1 / 2 : ℝ) with hgdef
  have hN20 : 0 ≤ N2 := by linarith
  have hηn : 0 ≤ η * n := by positivity
  have hεpos : 0 < 1 + η * n := by linarith
  by_cases hA : 2 ≤ x
  · left
    have hg4 : 1 / 4 ≤ g := by
      have : 1 / 4 ≤ x / (2 * (x + 2)) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have : n * b / 12 ≤ N2 * b * g := by
      have hb0 : 0 ≤ b := by linarith
      have h' : n / 3 * b * (1 / 4) ≤ N2 * b * g := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hb0) hg4 (by norm_num)
        positivity
      linarith
    nlinarith
  · push Not at hA
    have hg8 : x / 8 ≤ g := by
      have : x / 8 ≤ x / (2 * (x + 2)) := by
        apply div_le_div_of_nonneg_left hx0 (by positivity); linarith
      linarith
    by_cases hB : η * n ≤ 3
    · right
      have hε : 1 / 4 ≤ 1 / (1 + η * n) := by
        rw [div_le_div_iff₀ (by norm_num) hεpos]; linarith
      have : n * (P + 1) / 16 ≤ n * (P + 1) * (1 / (1 + η * n)) / 4 := by
        have := mul_le_mul_of_nonneg_left hε (show 0 ≤ n * (P + 1) by positivity)
        linarith
      nlinarith
    · push Not at hB
      have hηpos : 0 < η := by
        by_contra hcon
        push Not at hcon
        have : η = 0 := le_antisymm hcon hη
        rw [this] at hB; linarith
      -- lower bounds X and Y
      set X := n * b ^ 2 * η / 24 with hXdef
      set Y := 3 * (P + 1) / (16 * η) with hYdef
      have hX : X ≤ N2 * b * g := by
        have h' : n / 3 * b * (x / 8) ≤ N2 * b * g := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) hg8
            (by positivity)
          positivity
        have : X = n / 3 * b * (x / 8) := by rw [hXdef, hx]; ring
        linarith
      have hY : Y ≤ n * (P + 1) * (1 / (1 + η * n)) / 4 := by
        rw [hYdef, div_le_iff₀ (by positivity)]
        have hP1 : 0 < P + 1 := by linarith
        rw [show n * (P + 1) * (1 / (1 + η * n)) / 4 * (16 * η)
            = 4 * (P + 1) * (η * n) / (1 + η * n) by field_simp <;> norm_num]
        rw [le_div_iff₀ hεpos]
        nlinarith
      have hXY : (d * S / 100) ^ 2 ≤ X * Y := by
        have hXY' : X * Y = n * b ^ 2 * (P + 1) / 128 := by
          rw [hXdef, hYdef]; field_simp; ring
        rw [hXY', div_pow, mul_pow, hS2]
        have : 0 ≤ n := hn.le
        nlinarith
      by_contra hcon
      push Not at hcon
      have hX0 : 0 ≤ X := by positivity
      have hY0 : 0 ≤ Y := by positivity
      have hT0 : 0 ≤ d * S / 100 := by positivity
      have hXT : X < d * S / 100 := lt_of_le_of_lt hX hcon.1
      have hYT : Y < d * S / 100 := lt_of_le_of_lt hY hcon.2
      nlinarith [mul_le_mul hXT.le hYT.le hY0 hT0]

end
end Exp2FullProof

open Finset

namespace OnlineCombOpt.Exp2Full

theorem theorem_1_full_domain (n d : ℕ) (hnd : d ≤ n) (hd : d ≠ 1) :
    ∃ (A : Finset (Fin d → ℝ)) (m : ℕ), IsBinaryActionSet A m ∧
      ∀ η : ℝ, 0 ≤ η → ∃ z : ℕ → Fin d → ℝ,
        (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤ exp2Regret A η z n := by
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨{0}, 0, ?_, ?_⟩
    · simp [IsBinaryActionSet]
    · intro η _
      refine ⟨fun _ _ => 0, ?_, ?_⟩
      · intro t i
        norm_num
      · simp [exp2Regret, exp2ExpectedLoss, cumLoss, dotProduct]
  have hd2 : 2 ≤ d := by omega
  obtain ⟨hi1, hi2, hi3⟩ := Exp2FullProof.param_ineq d hd2
  set P := d / 2 / 3 with hP
  set b := 2 * (d / 2 / 3) + d / 2 % 3 with hbdef
  have hb : 0 < b := by omega
  have hcard : Fintype.card (Exp2FullProof.Lay P b (d - 2 * (d / 2))) = d := by
    simp only [Exp2FullProof.Lay, Fintype.card_sum, Fintype.card_fin]
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨Exp2FullProof.actSet e, P + b, Exp2FullProof.binary_actions e, ?_⟩
  intro η hη
  have hN2 : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 3 * (n / 2) by omega)
  have hfin := Exp2FullProof.final_ineq (n : ℝ) (d : ℝ) (b : ℝ) (P : ℝ) ((n / 2 : ℕ) : ℝ) η
    (by exact_mod_cast hd2) (by exact_mod_cast hnd) (by exact_mod_cast hb)
    (Nat.cast_nonneg _) hN2 (by exact_mod_cast hi1) (by exact_mod_cast hi2)
    (by exact_mod_cast hi3) hη
  rcases hfin with h | h
  · refine ⟨Exp2FullProof.altZ e n, Exp2FullProof.alt_losses_mem e n, ?_⟩
    rw [Exp2FullProof.alt_regret e hb n η]
    exact h
  · have hεpos : 0 < 1 + η * n := by positivity
    have hε0 : 0 ≤ 1 / (1 + η * (n : ℝ)) := by positivity
    have hε1 : 1 / (1 + η * (n : ℝ)) ≤ 1 := by
      rw [div_le_one hεpos]; nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n)]
    refine ⟨Exp2FullProof.smallZ e (1 / (1 + η * n)),
      Exp2FullProof.small_losses_mem e hb _ hε0 hε1, ?_⟩
    have hcut : η * (n : ℝ) * (1 / (1 + η * n)) ≤ 1 := by
      rw [mul_one_div, div_le_one hεpos]; linarith
    exact h.trans (Exp2FullProof.small_regret_lower e hb n η _ hη hε0 hcut)

end OnlineCombOpt.Exp2Full

open OnlineCombOpt.Exp2LB

theorem solution (n d : ℕ) (hnd : d ≤ n) (hd : d ≠ 1) :
    ∃ (A : Finset (Fin d → ℝ)) (m : ℕ), IsBinaryActionSet A m ∧
      ∀ η : ℝ, 0 ≤ η → ∃ z : ℕ → Fin d → ℝ,
        (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤ exp2Regret A η z n :=
  OnlineCombOpt.Exp2Full.theorem_1_full_domain n d hnd hd
