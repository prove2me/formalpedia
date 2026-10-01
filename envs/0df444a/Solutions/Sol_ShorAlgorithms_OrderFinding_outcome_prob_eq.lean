-- Prove2me | solution 1 for ShorAlgorithms.OrderFinding.outcome_prob_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:12:24.8408+00:00
-- url     : https://prove2.me/submissions/17a029c6-d329-485a-9791-ba0670be7330

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_outcomeProb
open ShorAlgorithms.OrderFinding ShorAlgorithms.Shared
namespace AShorOrder
lemma sqrt_inv_sq (q : ℕ) : ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  rfl

lemma amplitude (n x q : ℕ) (c : Fin q) (y : ZMod n) :
    finalState n x q (c, y) = (1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (Fin q)).filter
      (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = y),
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ)) := by
  classical
  simp only [finalState, preFourierState, fourierMatrix, Finset.sum_filter, Finset.mul_sum, one_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (x : ZMod n) ^ (a : ℕ) = y
  · simp only [h, if_true, ← mul_assoc, sqrt_inv_sq]
  · simp [h]

lemma mod_sum {q r k : ℕ} (hr : 0 < r) (hk : k < r) (hkq : k < q) (F : ℕ → ℂ) :
    (∑ a ∈ (Finset.univ : Finset (Fin q)).filter (fun a : Fin q => (a : ℕ) % r = k), F (a : ℕ)) =
      ∑ b ∈ Finset.range ((q - k - 1) / r + 1), F (b * r + k) := by
  classical
  apply Finset.sum_bij (fun (a : Fin q) _ => (a : ℕ) / r)
  · intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    have he : (a : ℕ) / r * r + k = a := by
      simpa [ha', Nat.mul_comm] using Nat.div_add_mod (a : ℕ) r
    simp only [Finset.mem_range, Nat.lt_add_one_iff]
    apply (Nat.le_div_iff_mul_le hr).mpr
    omega
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    have ea := Nat.mod_add_div (a : ℕ) r
    have eb := Nat.mod_add_div (b : ℕ) r
    rw [ha'] at ea
    rw [hb', ← hab] at eb
    omega
  · intro b hb
    have hb' : b * r ≤ q - k - 1 := (Nat.le_div_iff_mul_le hr).mp (Nat.le_of_lt_succ (Finset.mem_range.mp hb))
    have hbound : b * r + k < q := by omega
    refine ⟨⟨b * r + k, hbound⟩, ?_, ?_⟩
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
    · change (b * r + k) / r = b
      rw [Nat.mul_comm b r, Nat.mul_add_div hr, Nat.div_eq_of_lt hk, add_zero]
  · intro a ha
    congr 1
    have ha' := (Finset.mem_filter.mp ha).2
    simpa [ha', Nat.mul_comm] using (Nat.div_add_mod (a : ℕ) r).symm

lemma prob_formula (n x q l : ℕ) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2)
    (c : Fin q) (k : ℕ) (hk : k < orderOf (x : ZMod n)) :
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (Fin q)).filter
            (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = (x : ZMod n) ^ k),
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 ∧
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ b ∈ Finset.range ((q - k - 1) / orderOf (x : ZMod n) + 1),
          Complex.exp (2 * Real.pi * Complex.I *
            (((b * orderOf (x : ZMod n) + k : ℕ)) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by intro he; subst n; simp at hq2
  haveI : NeZero n := ⟨hn0⟩
  have hxfin : IsOfFinOrder (x : ZMod n) := ((ZMod.isUnit_iff_coprime x n).mpr hx).isOfFinOrder
  have hrn : orderOf (x : ZMod n) ≤ n := by simpa using (orderOf_le_card_univ (x := (x : ZMod n)))
  have hkq : k < q := lt_of_lt_of_le hk (hrn.trans ((Nat.le_self_pow (by norm_num : 2 ≠ 0) n).trans hnq))
  have hfilter : (Finset.univ : Finset (Fin q)).filter (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = (x : ZMod n) ^ k) =
      Finset.univ.filter (fun a : Fin q => (a : ℕ) % orderOf (x : ZMod n) = k) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hxfin.pow_inj_mod, Nat.mod_eq_of_lt hk]
  rw [outcomeProb, amplitude]
  refine ⟨rfl, ?_⟩
  rw [hfilter, mod_sum hxfin.orderOf_pos hk hkq (fun a => Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (c : ℕ) / (q : ℂ)))]

end AShorOrder

theorem solution (n x q l : ℕ) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2)
    (c : Fin q) (k : ℕ) (hk : k < orderOf (x : ZMod n)) :
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (Fin q)).filter
            (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = (x : ZMod n) ^ k),
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 ∧
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ b ∈ Finset.range ((q - k - 1) / orderOf (x : ZMod n) + 1),
          Complex.exp (2 * Real.pi * Complex.I *
            (((b * orderOf (x : ZMod n) + k : ℕ)) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2  := AShorOrder.prob_formula n x q l hx hq hnq hq2 c k hk
