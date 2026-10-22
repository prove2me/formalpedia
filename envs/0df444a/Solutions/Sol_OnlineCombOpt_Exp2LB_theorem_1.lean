-- Prove2me | solution 1 for OnlineCombOpt.Exp2LB.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T04:36:48.965721+00:00
-- url     : https://prove2.me/submissions/ee58c0ce-ca2e-47e5-808d-70f5a5cbc18e

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset
open Finset
open OnlineCombOpt.Exp2LB

namespace Exp2LowerBoundProof
noncomputable section
open scoped BigOperators

def bitReal (b : Bool) : ℝ := if b then 1 else 0

def quarter (k : ℕ) (i : Fin (4 * k)) : Fin 4 :=
  ((finProdFinEquiv : Fin 4 × Fin k ≃ Fin (4 * k)).symm i).1

def slot (k : ℕ) (i : Fin (4 * k)) : Fin k :=
  ((finProdFinEquiv : Fin 4 × Fin k ≃ Fin (4 * k)).symm i).2

def pairedAction (k : ℕ) (b : Fin (k + 1) → Bool) : Fin (4 * k) → ℝ :=
  fun i => if quarter k i = 0 then 1 - bitReal (b (slot k i).castSucc)
    else if quarter k i = 1 then bitReal (b (slot k i).castSucc)
    else if quarter k i = 2 then 1 - bitReal (b (Fin.last k))
    else bitReal (b (Fin.last k))

def pairedSet (k : ℕ) : Finset (Fin (4 * k) → ℝ) :=
  Finset.univ.image (pairedAction k)

def smallLoss (k : ℕ) (epsilon : ℝ) : ℕ → Fin (4 * k) → ℝ :=
  fun _ i => if quarter k i = 1 then epsilon else 0

def alternatingLoss (k n : ℕ) : ℕ → Fin (4 * k) → ℝ :=
  fun t i => if t < 2 * (n / 2) ∧
    ((Even t ∧ quarter k i = 2) ∨ (Odd t ∧ quarter k i = 3)) then 1 else 0

end
end Exp2LowerBoundProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2LowerBoundProof
noncomputable section

@[simp] theorem quarter_coord (k : ℕ) (q : Fin 4) (j : Fin k) :
    quarter k (finProdFinEquiv (q, j)) = q := by simp [quarter]
@[simp] theorem slot_coord (k : ℕ) (q : Fin 4) (j : Fin k) :
    slot k (finProdFinEquiv (q, j)) = j := by simp [slot]

@[simp] theorem bitReal_inj (b c : Bool) : bitReal b = bitReal c ↔ b = c := by
  cases b <;> cases c <;> norm_num [bitReal]

theorem pairedAction_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective (pairedAction k) := by
  intro b c h
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have hh := congrFun h (finProdFinEquiv ((3 : Fin 4), (⟨0, hk⟩ : Fin k)))
    simpa [pairedAction] using hh
  · have hh := congrFun h (finProdFinEquiv ((1 : Fin 4), i))
    simpa [pairedAction] using hh

theorem sum_coords (k : ℕ) (F : Fin (4 * k) → ℝ) :
    ∑ i, F i = ∑ j : Fin k,
      (F (finProdFinEquiv ((0 : Fin 4), j)) +
       F (finProdFinEquiv ((1 : Fin 4), j)) +
       F (finProdFinEquiv ((2 : Fin 4), j)) +
       F (finProdFinEquiv ((3 : Fin 4), j))) := by
  rw [← (finProdFinEquiv : Fin 4 × Fin k ≃ Fin (4 * k)).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_four]

theorem paired_dot (k : ℕ) (b : Fin (k + 1) → Bool) (z : Fin (4 * k) → ℝ) :
    pairedAction k b ⬝ᵥ z = ∑ j : Fin k,
      ((1 - bitReal (b j.castSucc)) * z (finProdFinEquiv ((0 : Fin 4), j)) +
       bitReal (b j.castSucc) * z (finProdFinEquiv ((1 : Fin 4), j)) +
       (1 - bitReal (b (Fin.last k))) * z (finProdFinEquiv ((2 : Fin 4), j)) +
       bitReal (b (Fin.last k)) * z (finProdFinEquiv ((3 : Fin 4), j))) := by
  rw [dotProduct, sum_coords]
  simp [pairedAction]

theorem binary_actions (k : ℕ) : IsBinaryActionSet (pairedSet k) (2 * k) := by
  classical
  constructor
  · exact ⟨pairedAction k (fun _ => false), mem_image.mpr ⟨_, mem_univ _, rfl⟩⟩
  intro a ha
  obtain ⟨b, _, rfl⟩ := mem_image.mp ha
  constructor
  · intro i
    simp only [pairedAction]
    split_ifs <;> cases hb : b (slot k i).castSucc <;>
      cases hc : b (Fin.last k) <;> simp [bitReal]
  · rw [sum_coords]
    have h : ∀ j : Fin k,
        pairedAction k b (finProdFinEquiv ((0 : Fin 4), j)) +
        pairedAction k b (finProdFinEquiv ((1 : Fin 4), j)) +
        pairedAction k b (finProdFinEquiv ((2 : Fin 4), j)) +
        pairedAction k b (finProdFinEquiv ((3 : Fin 4), j)) = 2 := by
      intro j
      simp [pairedAction]
      ring
    simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
      Nat.cast_ofNat]
    ring

theorem sum_actions (k : ℕ) (hk : 0 < k) (F : (Fin (4 * k) → ℝ) → ℝ) :
    ∑ a ∈ pairedSet k, F a = ∑ b : Fin (k + 1) → Bool, F (pairedAction k b) := by
  classical
  exact sum_image (fun a _ b _ hab => pairedAction_injective k hk hab)

end
end Exp2LowerBoundProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2LowerBoundProof
noncomputable section

 theorem partition_pos {d : ℕ} (A : Finset (Fin d → ℝ)) (hA : A.Nonempty)
    (eta : ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    0 < ∑ a ∈ A, Real.exp (-eta * cumLoss a z t) := by
  exact sum_pos (fun _ _ => Real.exp_pos _) hA

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

 theorem weights_sum {d : ℕ} (A : Finset (Fin d → ℝ)) (hA : A.Nonempty)
    (eta : ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    ∑ a ∈ A, exp2Weights A eta z t a = 1 := by
  calc
    _ = ∑ a ∈ A, Real.exp (-eta * cumLoss a z t) /
        (∑ b ∈ A, Real.exp (-eta * cumLoss b z t)) :=
      sum_congr rfl (fun a ha => gibbs_weights A hA eta z t a ha)
    _ = 1 := by rw [← sum_div, div_self (partition_pos A hA eta z t).ne']

end
end Exp2LowerBoundProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2LowerBoundProof
noncomputable section

private def bitProb (eta c : ℝ) (b : Bool) : ℝ :=
  Real.exp (-eta * c * bitReal b) / (1 + Real.exp (-eta * c))

private theorem bitProb_sum (eta c : ℝ) : ∑ b : Bool, bitProb eta c b = 1 := by
  have hp : 0 < 1 + Real.exp (-eta * c) := by positivity
  simp [bitProb, bitReal]
  field_simp
  ring

private theorem bitProb_true (eta c : ℝ) : bitProb eta c true = 1 / (1 + Real.exp (eta * c)) := by
  have hp : 0 < Real.exp (eta * c) := Real.exp_pos _
  have hq : 0 < 1 + Real.exp (eta * c) := by positivity
  simp only [bitProb, bitReal, if_true, mul_one]
  rw [show -eta * c = -(eta * c) by ring, Real.exp_neg]
  field_simp
  ring

private theorem product_probability_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (eta : ℝ) (c : ι → ℝ) :
    ∑ b : ι → Bool, ∏ j, bitProb eta (c j) (b j) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [bitProb_sum, prod_const_one]

private theorem product_probability_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (eta : ℝ) (c : ι → ℝ) (j : ι) :
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

private theorem exponential_product {ι : Type*} [Fintype ι]
    (eta c0 : ℝ) (c : ι → ℝ) (b : ι → Bool) :
    Real.exp (-eta * (c0 + ∑ j, c j * bitReal (b j))) =
      Real.exp (-eta * c0) * ∏ j, Real.exp (-eta * c j * bitReal (b j)) := by
  rw [mul_add, Real.exp_add, mul_sum, Real.exp_sum]
  congr 1
  apply prod_congr rfl
  intro j _
  congr 1
  ring

private theorem normalized_product {ι : Type*} [Fintype ι] [DecidableEq ι]
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

 theorem paired_step_mean (k : ℕ) (hk : 0 < k) (eta : ℝ)
    (z : ℕ → Fin (4 * k) → ℝ) (t : ℕ) (c0 : ℝ) (c : Fin (k + 1) → ℝ)
    (r0 : ℝ) (r : Fin (k + 1) → ℝ)
    (hc : ∀ b, cumLoss (pairedAction k b) z t = c0 + ∑ j, c j * bitReal (b j))
    (hr : ∀ b, pairedAction k b ⬝ᵥ z t = r0 + ∑ j, r j * bitReal (b j)) :
    ∑ a ∈ pairedSet k, exp2Weights (pairedSet k) eta z t a * (a ⬝ᵥ z t) =
      r0 + ∑ j, r j / (1 + Real.exp (eta * c j)) := by
  classical
  have hA := (binary_actions k).1
  have hw : ∀ b, exp2Weights (pairedSet k) eta z t (pairedAction k b) =
      ∏ j, bitProb eta (c j) (b j) := by
    intro b
    rw [gibbs_weights _ hA _ _ _ _ (mem_image.mpr ⟨b, mem_univ _, rfl⟩),
      sum_actions k hk]
    simp_rw [hc]
    exact normalized_product eta c0 c b
  rw [sum_actions k hk]
  simp_rw [hw, hr, mul_add, mul_sum]
  rw [sum_add_distrib, ← sum_mul, product_probability_sum, one_mul, sum_comm]
  congr 1
  apply sum_congr rfl
  intro j _
  simp_rw [show ∀ b : Fin (k + 1) → Bool,
    (∏ i, bitProb eta (c i) (b i)) * (r j * bitReal (b j)) =
      r j * ((∏ i, bitProb eta (c i) (b i)) * bitReal (b j)) by intro b; ring]
  rw [← mul_sum, product_probability_mean]
  ring

end
end Exp2LowerBoundProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2LowerBoundProof
noncomputable section
open scoped BigOperators

theorem loss_sum_coordinates (k : ℕ) (f : Fin (4 * k) → ℝ) :
    ∑ i, f i = ∑ q : Fin 4, ∑ j : Fin k, f (finProdFinEquiv (q, j)) := by
  simpa only [Fintype.sum_prod_type] using
    (Equiv.sum_comp (finProdFinEquiv : Fin 4 × Fin k ≃ Fin (4 * k)) f).symm

theorem small_dot (k : ℕ) (b : Fin (k + 1) → Bool) (ε : ℝ) (t : ℕ) :
    pairedAction k b ⬝ᵥ smallLoss k ε t =
      ε * ∑ j : Fin k, bitReal (b j.castSucc) := by
  unfold dotProduct
  rw [loss_sum_coordinates]
  simp [pairedAction, smallLoss, quarter, slot, Fin.sum_univ_succ,
    Finset.mul_sum, mul_comm]

theorem small_losses_mem (k : ℕ) (ε : ℝ) (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    ∀ t i, smallLoss k ε t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t i
  simp only [smallLoss]
  split_ifs
  · exact ⟨he, he1⟩
  · norm_num

theorem alternating_losses_mem (k n : ℕ) :
    ∀ t i, alternatingLoss k n t i ∈ Set.Icc (0 : ℝ) 1 := by
  intro t i
  simp only [alternatingLoss]
  split_ifs <;> norm_num

theorem alternating_dot_even (k n j : ℕ) (hj : j < n / 2)
    (b : Fin (k + 1) → Bool) :
    pairedAction k b ⬝ᵥ alternatingLoss k n (2 * j) =
      (k : ℝ) * (1 - bitReal (b (Fin.last k))) := by
  have he : Even (2 * j) := ⟨j, by omega⟩
  have ho : ¬ Odd (2 * j) := by rintro ⟨u, hu⟩; omega
  have ht : 2 * j < 2 * (n / 2) := by omega
  unfold dotProduct
  rw [loss_sum_coordinates]
  simp [pairedAction, alternatingLoss, quarter, slot, he, ho, ht]
  ring

theorem alternating_dot_odd (k n j : ℕ) (hj : j < n / 2)
    (b : Fin (k + 1) → Bool) :
    pairedAction k b ⬝ᵥ alternatingLoss k n (2 * j + 1) =
      (k : ℝ) * bitReal (b (Fin.last k)) := by
  have ho : Odd (2 * j + 1) := ⟨j, by omega⟩
  have he : ¬ Even (2 * j + 1) := by rintro ⟨u, hu⟩; omega
  have ht : 2 * j + 1 < 2 * (n / 2) := by omega
  unfold dotProduct
  rw [loss_sum_coordinates]
  simp [pairedAction, alternatingLoss, quarter, slot, he, ho, ht]

theorem alternating_dot_after (k n t : ℕ) (ht : 2 * (n / 2) ≤ t)
    (a : Fin (4 * k) → ℝ) : a ⬝ᵥ alternatingLoss k n t = 0 := by
  simp [dotProduct, alternatingLoss, not_lt.mpr ht]

theorem loss_cum_succ {d : ℕ} (a : Fin d → ℝ) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    cumLoss a z (t + 1) = cumLoss a z t + a ⬝ᵥ z t := by
  simp only [cumLoss, sum_range_succ]

theorem small_cum (k : ℕ) (b : Fin (k + 1) → Bool) (ε : ℝ) (t : ℕ) :
    cumLoss (pairedAction k b) (smallLoss k ε) t =
      (t : ℝ) * ε * ∑ j : Fin k, bitReal (b j.castSucc) := by
  simp only [cumLoss, small_dot, sum_const, card_range, nsmul_eq_mul]
  ring

theorem alternating_cum_even (k n : ℕ) (b : Fin (k + 1) → Bool)
    (j : ℕ) (hj : j ≤ n / 2) :
    cumLoss (pairedAction k b) (alternatingLoss k n) (2 * j) = (j : ℝ) * k := by
  induction j with
  | zero => simp [cumLoss]
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, loss_cum_succ,
      loss_cum_succ, ih (by omega), alternating_dot_even k n j (by omega),
      alternating_dot_odd k n j (by omega)]
    push_cast
    ring

theorem alternating_cum_odd (k n : ℕ) (b : Fin (k + 1) → Bool)
    (j : ℕ) (hj : j < n / 2) :
    cumLoss (pairedAction k b) (alternatingLoss k n) (2 * j + 1) =
      ((j : ℝ) + 1) * k - k * bitReal (b (Fin.last k)) := by
  rw [loss_cum_succ, alternating_cum_even k n b j (by omega),
    alternating_dot_even k n j hj]
  ring

theorem loss_cum_eq_of_after {d : ℕ} (a : Fin d → ℝ) (z : ℕ → Fin d → ℝ)
    (m n : ℕ) (hmn : m ≤ n) (hz : ∀ t, m ≤ t → a ⬝ᵥ z t = 0) :
    cumLoss a z n = cumLoss a z m := by
  symm
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro t _ htm
  exact hz t (by simpa only [mem_range, not_lt] using htm)

theorem alternating_cum_horizon (k n : ℕ) (b : Fin (k + 1) → Bool) :
    cumLoss (pairedAction k b) (alternatingLoss k n) n = ((n / 2 : ℕ) : ℝ) * k := by
  rw [loss_cum_eq_of_after (pairedAction k b) (alternatingLoss k n)
    (2 * (n / 2)) n (by omega) (fun t ht => alternating_dot_after k n t ht _)]
  exact alternating_cum_even k n b (n / 2) le_rfl

end
end Exp2LowerBoundProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2LowerBoundProof
noncomputable section
open scoped BigOperators

def localCoeff (k : ℕ) (x : ℝ) (j : Fin (k + 1)) : ℝ :=
  if j = Fin.last k then 0 else x

def lastCoeff (k : ℕ) (x : ℝ) (j : Fin (k + 1)) : ℝ :=
  if j = Fin.last k then x else 0

theorem localCoeff_sum (k : ℕ) (x : ℝ) (f : Fin (k + 1) → ℝ) :
    ∑ j, localCoeff k x j * f j = x * ∑ j : Fin k, f j.castSucc := by
  rw [Fin.sum_univ_castSucc]
  simp [localCoeff, Finset.mul_sum]

theorem lastCoeff_sum (k : ℕ) (x : ℝ) (f : Fin (k + 1) → ℝ) :
    ∑ j, lastCoeff k x j * f j = x * f (Fin.last k) := by
  simp [lastCoeff]

theorem small_mean (k : ℕ) (hk : 0 < k) (n : ℕ) (η ε : ℝ) :
    ∑ a ∈ pairedSet k, exp2Weights (pairedSet k) η (smallLoss k ε) n a *
      (a ⬝ᵥ smallLoss k ε n) = (k : ℝ) * ε / (1 + Real.exp (η * (n : ℝ) * ε)) := by
  have hc : ∀ b, cumLoss (pairedAction k b) (smallLoss k ε) n =
      0 + ∑ j, localCoeff k ((n : ℝ) * ε) j * bitReal (b j) := by
    intro b
    rw [localCoeff_sum, zero_add, small_cum]
  have hr : ∀ b, pairedAction k b ⬝ᵥ smallLoss k ε n =
      0 + ∑ j, localCoeff k ε j * bitReal (b j) := by
    intro b
    rw [localCoeff_sum, zero_add, small_dot]
  have h := paired_step_mean k hk η (smallLoss k ε) n 0
    (localCoeff k ((n : ℝ) * ε)) 0 (localCoeff k ε) hc hr
  simpa [Fin.sum_univ_castSucc, localCoeff, mul_assoc, mul_div_assoc] using h

theorem small_regret (k : ℕ) (hk : 0 < k) (n : ℕ) (η ε : ℝ) (he : 0 ≤ ε) :
    exp2Regret (pairedSet k) η (smallLoss k ε) n =
      ∑ t ∈ Finset.range n, (k : ℝ) * ε / (1 + Real.exp (η * (t : ℝ) * ε)) := by
  classical
  have hA := (binary_actions k).1
  have hmin : (pairedSet k).inf' hA (fun a => cumLoss a (smallLoss k ε) n) = 0 := by
    apply le_antisymm
    · have hm : pairedAction k (fun _ => false) ∈ pairedSet k :=
        mem_image_of_mem _ (mem_univ _)
      calc
        _ ≤ cumLoss (pairedAction k (fun _ => false)) (smallLoss k ε) n :=
          Finset.inf'_le (fun a => cumLoss a (smallLoss k ε) n) hm
        _ = 0 := by simp [small_cum, bitReal]
    · apply Finset.le_inf'
      intro a ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      rw [small_cum]
      apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he)
      apply sum_nonneg
      intro j _
      simp only [bitReal]
      split_ifs <;> norm_num
  simp only [exp2Regret, dif_pos hA, hmin, sub_zero, exp2ExpectedLoss, small_mean k hk]

theorem alternating_mean_even (k : ℕ) (hk : 0 < k) (n j : ℕ)
    (hj : j < n / 2) (η : ℝ) :
    ∑ a ∈ pairedSet k, exp2Weights (pairedSet k) η (alternatingLoss k n) (2 * j) a *
      (a ⬝ᵥ alternatingLoss k n (2 * j)) = (k : ℝ) / 2 := by
  have hc : ∀ b, cumLoss (pairedAction k b) (alternatingLoss k n) (2 * j) =
      (j : ℝ) * k + ∑ l, (0 : ℝ) * bitReal (b l) := by
    intro b
    simpa using alternating_cum_even k n b j (by omega)
  have hr : ∀ b, pairedAction k b ⬝ᵥ alternatingLoss k n (2 * j) =
      (k : ℝ) + ∑ l, lastCoeff k (-(k : ℝ)) l * bitReal (b l) := by
    intro b
    rw [lastCoeff_sum, alternating_dot_even k n j hj]
    ring
  have h := paired_step_mean k hk η (alternatingLoss k n) (2 * j)
    ((j : ℝ) * k) (fun _ => 0) k (lastCoeff k (-(k : ℝ))) hc hr
  calc
    _ = (k : ℝ) + (-(k : ℝ)) / 2 := by simpa [lastCoeff, ite_div, show (1 : ℝ) + 1 = 2 by norm_num] using h
    _ = _ := by ring

theorem alternating_mean_odd (k : ℕ) (hk : 0 < k) (n j : ℕ)
    (hj : j < n / 2) (η : ℝ) :
    ∑ a ∈ pairedSet k, exp2Weights (pairedSet k) η (alternatingLoss k n) (2 * j + 1) a *
      (a ⬝ᵥ alternatingLoss k n (2 * j + 1)) =
        (k : ℝ) * Real.exp (η * k) / (1 + Real.exp (η * k)) := by
  have hc : ∀ b, cumLoss (pairedAction k b) (alternatingLoss k n) (2 * j + 1) =
      ((j : ℝ) + 1) * k + ∑ l, lastCoeff k (-(k : ℝ)) l * bitReal (b l) := by
    intro b
    rw [lastCoeff_sum, alternating_cum_odd k n b j hj]
    ring
  have hr : ∀ b, pairedAction k b ⬝ᵥ alternatingLoss k n (2 * j + 1) =
      0 + ∑ l, lastCoeff k (k : ℝ) l * bitReal (b l) := by
    intro b
    rw [lastCoeff_sum, zero_add, alternating_dot_odd k n j hj]
  have h := paired_step_mean k hk η (alternatingLoss k n) (2 * j + 1)
    (((j : ℝ) + 1) * k) (lastCoeff k (-(k : ℝ))) 0 (lastCoeff k k) hc hr
  have h' : (∑ a ∈ pairedSet k, exp2Weights (pairedSet k) η (alternatingLoss k n)
      (2 * j + 1) a * (a ⬝ᵥ alternatingLoss k n (2 * j + 1))) =
      (k : ℝ) / (1 + Real.exp (-(η * k))) := by
    have ht : ∀ l, lastCoeff k (k : ℝ) l /
        (1 + Real.exp (η * lastCoeff k (-(k : ℝ)) l)) =
        if l = Fin.last k then (k : ℝ) / (1 + Real.exp (-(η * k))) else 0 := by
      intro l
      by_cases hl : l = Fin.last k <;> simp [lastCoeff, hl]
    simpa only [ht, sum_ite_eq', mem_univ, if_true, zero_add] using h
  rw [h', Real.exp_neg]
  have he := Real.exp_pos (η * k)
  field_simp
  ring

theorem alternating_expected_pairs (k : ℕ) (hk : 0 < k) (n j : ℕ)
    (hj : j ≤ n / 2) (η : ℝ) :
    exp2ExpectedLoss (pairedSet k) η (alternatingLoss k n) (2 * j) =
      (j : ℝ) * ((k : ℝ) / 2 + k * Real.exp (η * k) / (1 + Real.exp (η * k))) := by
  induction j with
  | zero => simp [exp2ExpectedLoss]
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega]
    simp only [exp2ExpectedLoss, sum_range_succ]
    rw [← exp2ExpectedLoss, ih (by omega), alternating_mean_even k hk n j (by omega),
      alternating_mean_odd k hk n j (by omega)]
    push_cast
    ring

theorem alternating_regret (k : ℕ) (hk : 0 < k) (n : ℕ) (η : ℝ) :
    exp2Regret (pairedSet k) η (alternatingLoss k n) n =
      ((n / 2 : ℕ) : ℝ) * k *
        (Real.exp (η * k) / (1 + Real.exp (η * k)) - (1 / 2 : ℝ)) := by
  classical
  have hA := (binary_actions k).1
  have hc : ∀ a ∈ pairedSet k, cumLoss a (alternatingLoss k n) n =
      ((n / 2 : ℕ) : ℝ) * k := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := mem_image.mp ha
    exact alternating_cum_horizon k n b
  have hmin : (pairedSet k).inf' hA (fun a => cumLoss a (alternatingLoss k n) n) =
      ((n / 2 : ℕ) : ℝ) * k := by
    apply le_antisymm
    · obtain ⟨a, ha⟩ := hA
      simpa only [hc a ha] using Finset.inf'_le (fun a => cumLoss a (alternatingLoss k n) n) ha
    · exact Finset.le_inf' hA _ (fun a ha => (hc a ha).ge)
  have he : exp2ExpectedLoss (pairedSet k) η (alternatingLoss k n) n =
      exp2ExpectedLoss (pairedSet k) η (alternatingLoss k n) (2 * (n / 2)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (show 2 * (n / 2) ≤ n by omega))
    intro t _ ht
    have ht' : 2 * (n / 2) ≤ t := by simpa only [mem_range, not_lt] using ht
    simp only [alternating_dot_after k n t ht', mul_zero, sum_const_zero]
  rw [exp2Regret, dif_pos hA, hmin, he, alternating_expected_pairs k hk n (n / 2) le_rfl]
  ring

end
end Exp2LowerBoundProof

open Finset OnlineCombOpt.Exp2LB
namespace Exp2LowerBoundProof
noncomputable section
open scoped BigOperators

theorem logistic_lower (a x : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hax : a ≤ x) :
    a / 8 ≤ Real.exp x / (1 + Real.exp x) - (1 / 2 : ℝ) := by
  have hE : 1 + a ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hp := mul_nonneg (show 0 ≤ 4 - a by linarith) (sub_nonneg.mpr hE)
  have hq := mul_nonneg ha (show 0 ≤ 1 - a by linarith)
  rw [le_sub_iff_add_le, le_div_iff₀ (show 0 < 1 + Real.exp x by positivity)]
  nlinarith

theorem small_regret_lower (k : ℕ) (hk : 0 < k) (n : ℕ) (η ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hcut : η * (n : ℝ) * ε ≤ 1) :
    (n : ℝ) * k * ε / 4 ≤ exp2Regret (pairedSet k) η (smallLoss k ε) n := by
  rw [small_regret k hk n η ε hε]
  calc
    (n : ℝ) * k * ε / 4 = ∑ _t ∈ Finset.range n, (k : ℝ) * ε / 4 := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring
    _ ≤ ∑ t ∈ Finset.range n, (k : ℝ) * ε / (1 + Real.exp (η * (t : ℝ) * ε)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htn : (t : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt (mem_range.mp ht))
      have hz : η * (t : ℝ) * ε ≤ 1 :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htn hη) hε).trans hcut
      have he : Real.exp (η * (t : ℝ) * ε) ≤ 3 :=
        (Real.exp_le_exp.mpr hz).trans Real.exp_one_lt_three.le
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)).mpr
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) * ε by positivity) (show 0 ≤ 3 - Real.exp (η * (t : ℝ) * ε) by linarith)]

theorem paired_lower_bound (k : ℕ) (hk : 0 < k) (n : ℕ) (hkn : 4 * k ≤ n)
    (η : ℝ) (hη : 0 ≤ η) :
    ∃ z : ℕ → Fin (4 * k) → ℝ,
      (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 100 * (4 * k) * Real.sqrt (4 * k) * Real.sqrt n ≤
        exp2Regret (pairedSet k) η z n := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hknr : 4 * (k : ℝ) ≤ n := by exact_mod_cast hkn
  let a : ℝ := Real.sqrt ((4 * (k : ℝ)) / n)
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos (by positivity) hn)
  have hasq : a ^ 2 = (4 * (k : ℝ)) / n := Real.sq_sqrt (by positivity)
  have hna : (n : ℝ) * a ^ 2 = 4 * k := by
    have h := (eq_div_iff (ne_of_gt hn)).mp hasq
    nlinarith
  have ha2 : a ^ 2 ≤ 1 := by
    rw [hasq]
    exact (div_le_one hn).2 hknr
  have ha1 : a ≤ 1 := by nlinarith
  have hs : a * Real.sqrt n = Real.sqrt (4 * (k : ℝ)) := by
    dsimp [a]
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ (ne_of_gt hn)]
  have hscale : (n : ℝ) * a = Real.sqrt (4 * (k : ℝ)) * Real.sqrt n := by
    calc
      (n : ℝ) * a = (Real.sqrt n) ^ 2 * a := by rw [Real.sq_sqrt hn.le]
      _ = (a * Real.sqrt n) * Real.sqrt n := by ring
      _ = _ := by rw [hs]
  have htarget : (1 : ℝ) / 100 * (4 * k) * Real.sqrt (4 * k) * Real.sqrt n =
      ((n : ℝ) * k * a) / 25 := by
    calc
      (1 : ℝ) / 100 * (4 * k) * Real.sqrt (4 * k) * Real.sqrt n =
          (4 * (k : ℝ)) / 100 * (Real.sqrt (4 * k) * Real.sqrt n) := by ring
      _ = _ := by rw [← hscale]; ring
  have hprod : 0 ≤ (n : ℝ) * k * a := by positivity
  by_cases hcut : η * (n : ℝ) * (a / 4) ≤ 1
  · refine ⟨smallLoss k (a / 4), small_losses_mem k (a / 4) (by positivity) (by linarith), ?_⟩
    rw [htarget]
    have hb := small_regret_lower k hk n η (a / 4) hη (by positivity) hcut
    nlinarith
  · refine ⟨alternatingLoss k n, alternating_losses_mem k n, ?_⟩
    have hax : a ≤ η * k := by
      have h := mul_lt_mul_of_pos_right (lt_of_not_ge hcut) ha
      have he : η * (n : ℝ) * (a / 4) * a = η * k := by
        calc
          η * (n : ℝ) * (a / 4) * a = η * ((n : ℝ) * a ^ 2) / 4 := by ring
          _ = _ := by rw [hna]; ring
      rw [one_mul, he] at h
      exact h.le
    have hl := logistic_lower a (η * k) ha.le ha1 hax
    have hfloor : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 3 * (n / 2) by omega)
    have hscaled := mul_le_mul_of_nonneg_right hfloor (show 0 ≤ (k : ℝ) * a by positivity)
    rw [htarget, alternating_regret k hk n η]
    calc
      ((n : ℝ) * k * a) / 25 ≤ ((n / 2 : ℕ) : ℝ) * k * (a / 8) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

end
end Exp2LowerBoundProof

open Finset

namespace OnlineCombOpt.Exp2LB

/-- Theorem 1 (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2, p. 6): let `n ≥ d` (with `d` a multiple
of 4). There is an action set `A ⊆ {0,1}^d` with constant `‖a‖₁` such that, for every learning rate
`η ≥ 0`, some adversary with losses in `[0,1]^d` forces full-information EXP2 to regret
`R_n ≥ 0.01 d^{3/2} √n`. -/
theorem theorem_1 (n d : ℕ) (hd : 4 ∣ d) (hnd : d ≤ n) :
    ∃ (A : Finset (Fin d → ℝ)) (m : ℕ), IsBinaryActionSet A m ∧
      ∀ η : ℝ, 0 ≤ η → ∃ z : ℕ → Fin d → ℝ, (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤ exp2Regret A η z n := by
  obtain ⟨k, rfl⟩ := hd
  by_cases hk : k = 0
  · subst k
    refine ⟨{0}, 0, ?_, ?_⟩
    · simp [IsBinaryActionSet]
    · intro η _
      refine ⟨fun _ _ => 0, ?_, ?_⟩
      · intro t i
        norm_num
      · simp [exp2Regret, exp2ExpectedLoss, cumLoss, dotProduct]
  · refine ⟨Exp2LowerBoundProof.pairedSet k, 2 * k,
      Exp2LowerBoundProof.binary_actions k, ?_⟩
    intro η hη
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Exp2LowerBoundProof.paired_lower_bound k (Nat.pos_of_ne_zero hk) n hnd η hη


end OnlineCombOpt.Exp2LB

open OnlineCombOpt.Exp2LB

theorem solution (n d : ℕ) (hd : 4 ∣ d) (hnd : d ≤ n) :
    ∃ (A : Finset (Fin d → ℝ)) (m : ℕ), IsBinaryActionSet A m ∧
      ∀ η : ℝ, 0 ≤ η → ∃ z : ℕ → Fin d → ℝ, (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤ exp2Regret A η z n := by
  exact OnlineCombOpt.Exp2LB.theorem_1 n d hd hnd
