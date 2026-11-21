-- Prove2me | solution 1 for ProphetBipartite.step_contraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:42:21.389925+00:00
-- url     : https://prove2.me/submissions/79cf3839-7e82-4c11-b548-e3ef259f8b88

import Mathlib
import Definitions.Def_ProphetBipartite_algorithm1Step

namespace Aux_PBstep
open ProphetBipartite

theorem ent_pos (x c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ max (x + c * d / 2) 0 - max x 0 ∧ max (x + c * d / 2) 0 - max x 0 ≤ c * d / 2 := by
  have hcd : 0 ≤ c * d := mul_nonneg hc hd
  have h2 := le_max_right x 0
  have h5 : max (x + c * d / 2) 0 ≤ max x 0 + c * d / 2 :=
    max_le (by linarith [le_max_left x 0]) (by linarith)
  have h6 : max x 0 ≤ max (x + c * d / 2) 0 := max_le_max (by linarith) le_rfl
  constructor <;> linarith

theorem ent_neg (x c d : ℝ) (hc : 0 ≤ c) (hd : d ≤ 0) :
    c * d / 2 ≤ max (x + c * d / 2) 0 - max x 0 ∧ max (x + c * d / 2) 0 - max x 0 ≤ 0 := by
  have hcd : c * d ≤ 0 := by nlinarith
  have h5 : max (x + c * d / 2) 0 ≤ max x 0 := max_le_max (by linarith) le_rfl
  have h6 : max x 0 + c * d / 2 ≤ max (x + c * d / 2) 0 := by
    rcases le_total x 0 with h | h
    · rw [max_eq_right h]
      linarith [le_max_right (x + c * d / 2) 0]
    · rw [max_eq_left h]
      exact le_max_left _ _
  constructor <;> linarith

theorem row {J : Type*} [Fintype J] (x c D : J → ℝ) (d : ℝ) (hc : ∀ j, 0 ≤ c j)
    (hs : ∑ j, c j ≤ 1) (hD : ∀ j, D j = max (x j + c j * d / 2) 0 - max (x j) 0) :
    |d / 2 - ∑ j, D j| = |d| / 2 - ∑ j, |D j| := by
  have hcs : ∑ j, c j * d / 2 = (∑ j, c j) * (d / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hc0 : 0 ≤ ∑ j, c j := Finset.sum_nonneg (fun j _ => hc j)
  by_cases hd : 0 ≤ d
  · have hDb : ∀ j, 0 ≤ D j ∧ D j ≤ c j * d / 2 := fun j => by
      rw [hD j]; exact ent_pos (x j) (c j) d (hc j) hd
    have hle : ∑ j, D j ≤ ∑ j, c j * d / 2 := Finset.sum_le_sum (fun j _ => (hDb j).2)
    have hge : 0 ≤ ∑ j, D j := Finset.sum_nonneg (fun j _ => (hDb j).1)
    have hprod : (∑ j, c j) * (d / 2) ≤ d / 2 := by nlinarith
    have habs : ∑ j, |D j| = ∑ j, D j :=
      Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hDb j).1)
    rw [habs, abs_of_nonneg hd, abs_of_nonneg (by linarith)]
  · have hd' : d ≤ 0 := by linarith
    have hDb : ∀ j, c j * d / 2 ≤ D j ∧ D j ≤ 0 := fun j => by
      rw [hD j]; exact ent_neg (x j) (c j) d (hc j) hd'
    have hge : ∑ j, c j * d / 2 ≤ ∑ j, D j := Finset.sum_le_sum (fun j _ => (hDb j).1)
    have hle : ∑ j, D j ≤ 0 := Finset.sum_nonpos (fun j _ => (hDb j).2)
    have hprod : d / 2 ≤ (∑ j, c j) * (d / 2) := by nlinarith
    have habs : ∑ j, |D j| = ∑ j, -D j :=
      Finset.sum_congr rfl (fun j _ => abs_of_nonpos (hDb j).2)
    rw [habs, Finset.sum_neg_distrib, abs_of_nonpos hd', abs_of_nonpos (by linarith)]
    ring

theorem case1 {L R : Type*} [Fintype L] [Fintype R]
    (M Q : L → R → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) (l' : L → ℝ) (hl' : ∀ i, l' i = l i - 1 / 2 * deltaL M Q l r i) :
    error17 M Q l' r ≤ (∑ i, |deltaL M Q l r i|) / 2 + ∑ j, |deltaR M Q l r j| := by
  obtain ⟨D, hD⟩ : ∃ D : L → R → ℝ, ∀ i j, D i j =
      max (M i j - Q i j * (l' i + r j)) 0 - max (M i j - Q i j * (l i + r j)) 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hDent : ∀ i j, D i j = max ((M i j - Q i j * (l i + r j)) +
      Q i j * deltaL M Q l r i / 2) 0 - max (M i j - Q i j * (l i + r j)) 0 := by
    intro i j
    rw [hD, hl']
    rw [show M i j - Q i j * (l i - 1 / 2 * deltaL M Q l r i + r j) =
      (M i j - Q i j * (l i + r j)) + Q i j * deltaL M Q l r i / 2 by ring]
  have hrowres : ∀ i, |deltaL M Q l r i / 2 - ∑ j, D i j| =
      |deltaL M Q l r i| / 2 - ∑ j, |D i j| := fun i =>
    row (fun j => M i j - Q i j * (l i + r j)) (fun j => Q i j) (fun j => D i j)
      (deltaL M Q l r i) (fun j => hQ i j) (hrow i) (fun j => hDent i j)
  have hL : ∀ i, deltaL M Q l' r i = deltaL M Q l r i / 2 - ∑ j, D i j := by
    intro i
    have e : deltaL M Q l' r i = l' i - ∑ j, max (M i j - Q i j * (l' i + r j)) 0 := rfl
    have e0 : deltaL M Q l r i = l i - ∑ j, max (M i j - Q i j * (l i + r j)) 0 := rfl
    have eD : ∑ j, D i j = ∑ j, max (M i j - Q i j * (l' i + r j)) 0 -
        ∑ j, max (M i j - Q i j * (l i + r j)) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => hD i j)
    have := hl' i
    rw [e, eD]
    linarith
  have hR : ∀ j, deltaR M Q l' r j = deltaR M Q l r j - ∑ i, D i j := by
    intro j
    have e : deltaR M Q l' r j = r j - ∑ i, max (M i j - Q i j * (l' i + r j)) 0 := rfl
    have e0 : deltaR M Q l r j = r j - ∑ i, max (M i j - Q i j * (l i + r j)) 0 := rfl
    have eD : ∑ i, D i j = ∑ i, max (M i j - Q i j * (l' i + r j)) 0 -
        ∑ i, max (M i j - Q i j * (l i + r j)) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hD i j)
    rw [e, eD]
    linarith
  have h1 : ∑ i, |deltaL M Q l' r i| = ∑ i, |deltaL M Q l r i| / 2 - ∑ i, ∑ j, |D i j| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hL i]; exact hrowres i)
  have h2 : ∑ j, |deltaR M Q l' r j| ≤ ∑ j, |deltaR M Q l r j| + ∑ i, ∑ j, |D i j| := by
    calc ∑ j, |deltaR M Q l' r j| ≤ ∑ j, (|deltaR M Q l r j| + ∑ i, |D i j|) := by
          apply Finset.sum_le_sum
          intro j _
          rw [hR j]
          have hs := Finset.abs_sum_le_sum_abs (fun i => D i j) Finset.univ
          have ha1 := le_abs_self (deltaR M Q l r j)
          have ha2 := neg_abs_le (deltaR M Q l r j)
          have hb1 := le_abs_self (∑ i, D i j)
          have hb2 := neg_abs_le (∑ i, D i j)
          rw [abs_le]
          constructor <;> linarith
      _ = ∑ j, |deltaR M Q l r j| + ∑ j, ∑ i, |D i j| := Finset.sum_add_distrib
      _ = ∑ j, |deltaR M Q l r j| + ∑ i, ∑ j, |D i j| := by rw [Finset.sum_comm]
  have hdiv : ∑ i, |deltaL M Q l r i| / 2 = (∑ i, |deltaL M Q l r i|) / 2 :=
    (Finset.sum_div _ _ _).symm
  have herr : error17 M Q l' r = ∑ i, |deltaL M Q l' r i| + ∑ j, |deltaR M Q l' r j| := rfl
  rw [herr]
  linarith

theorem case2 {L R : Type*} [Fintype L] [Fintype R]
    (M Q : L → R → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (hcol : ∀ j, ∑ i, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) (r' : R → ℝ) (hr' : ∀ j, r' j = r j - 1 / 2 * deltaR M Q l r j) :
    error17 M Q l r' ≤ ∑ i, |deltaL M Q l r i| + (∑ j, |deltaR M Q l r j|) / 2 := by
  obtain ⟨D, hD⟩ : ∃ D : L → R → ℝ, ∀ i j, D i j =
      max (M i j - Q i j * (l i + r' j)) 0 - max (M i j - Q i j * (l i + r j)) 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hDent : ∀ i j, D i j = max ((M i j - Q i j * (l i + r j)) +
      Q i j * deltaR M Q l r j / 2) 0 - max (M i j - Q i j * (l i + r j)) 0 := by
    intro i j
    rw [hD, hr']
    rw [show M i j - Q i j * (l i + (r j - 1 / 2 * deltaR M Q l r j)) =
      (M i j - Q i j * (l i + r j)) + Q i j * deltaR M Q l r j / 2 by ring]
  have hcolres : ∀ j, |deltaR M Q l r j / 2 - ∑ i, D i j| =
      |deltaR M Q l r j| / 2 - ∑ i, |D i j| := fun j =>
    row (fun i => M i j - Q i j * (l i + r j)) (fun i => Q i j) (fun i => D i j)
      (deltaR M Q l r j) (fun i => hQ i j) (hcol j) (fun i => hDent i j)
  have hR : ∀ j, deltaR M Q l r' j = deltaR M Q l r j / 2 - ∑ i, D i j := by
    intro j
    have e : deltaR M Q l r' j = r' j - ∑ i, max (M i j - Q i j * (l i + r' j)) 0 := rfl
    have e0 : deltaR M Q l r j = r j - ∑ i, max (M i j - Q i j * (l i + r j)) 0 := rfl
    have eD : ∑ i, D i j = ∑ i, max (M i j - Q i j * (l i + r' j)) 0 -
        ∑ i, max (M i j - Q i j * (l i + r j)) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hD i j)
    have := hr' j
    rw [e, eD]
    linarith
  have hL : ∀ i, deltaL M Q l r' i = deltaL M Q l r i - ∑ j, D i j := by
    intro i
    have e : deltaL M Q l r' i = l i - ∑ j, max (M i j - Q i j * (l i + r' j)) 0 := rfl
    have e0 : deltaL M Q l r i = l i - ∑ j, max (M i j - Q i j * (l i + r j)) 0 := rfl
    have eD : ∑ j, D i j = ∑ j, max (M i j - Q i j * (l i + r' j)) 0 -
        ∑ j, max (M i j - Q i j * (l i + r j)) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => hD i j)
    rw [e, eD]
    linarith
  have h1 : ∑ j, |deltaR M Q l r' j| = ∑ j, |deltaR M Q l r j| / 2 - ∑ j, ∑ i, |D i j| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [hR j]; exact hcolres j)
  have h2 : ∑ i, |deltaL M Q l r' i| ≤ ∑ i, |deltaL M Q l r i| + ∑ j, ∑ i, |D i j| := by
    calc ∑ i, |deltaL M Q l r' i| ≤ ∑ i, (|deltaL M Q l r i| + ∑ j, |D i j|) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hL i]
          have hs := Finset.abs_sum_le_sum_abs (fun j => D i j) Finset.univ
          have ha1 := le_abs_self (deltaL M Q l r i)
          have ha2 := neg_abs_le (deltaL M Q l r i)
          have hb1 := le_abs_self (∑ j, D i j)
          have hb2 := neg_abs_le (∑ j, D i j)
          rw [abs_le]
          constructor <;> linarith
      _ = ∑ i, |deltaL M Q l r i| + ∑ i, ∑ j, |D i j| := Finset.sum_add_distrib
      _ = ∑ i, |deltaL M Q l r i| + ∑ j, ∑ i, |D i j| := by rw [Finset.sum_comm]
  have hdiv : ∑ j, |deltaR M Q l r j| / 2 = (∑ j, |deltaR M Q l r j|) / 2 :=
    (Finset.sum_div _ _ _).symm
  have herr : error17 M Q l r' = ∑ i, |deltaL M Q l r' i| + ∑ j, |deltaR M Q l r' j| := rfl
  rw [herr]
  linarith

theorem step_le {L R : Type*} [Fintype L] [Fintype R]
    (M Q : L → R → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hcol : ∀ j, ∑ i, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) :
    error17 M Q (algorithm1Step M Q (l, r)).1 (algorithm1Step M Q (l, r)).2 ≤
      (3 / 4) * error17 M Q l r := by
  have herr : error17 M Q l r = ∑ i, |deltaL M Q l r i| + ∑ j, |deltaR M Q l r j| := rfl
  by_cases h : ∑ j, |deltaR M Q l r j| ≤ ∑ i, |deltaL M Q l r i|
  · have hs : algorithm1Step M Q (l, r) = (fun i => l i - 1 / 2 * deltaL M Q l r i, r) := by
      unfold algorithm1Step
      exact if_pos h
    have c1 := case1 M Q hQ hrow l r (fun i => l i - 1 / 2 * deltaL M Q l r i) (fun i => rfl)
    rw [hs]
    show error17 M Q (fun i => l i - 1 / 2 * deltaL M Q l r i) r ≤ _
    linarith
  · have hs : algorithm1Step M Q (l, r) = (l, fun j => r j - 1 / 2 * deltaR M Q l r j) := by
      unfold algorithm1Step
      exact if_neg h
    have c2 := case2 M Q hQ hcol l r (fun j => r j - 1 / 2 * deltaR M Q l r j) (fun j => rfl)
    have h' := not_le.mp h
    rw [hs]
    show error17 M Q l (fun j => r j - 1 / 2 * deltaR M Q l r j) ≤ _
    linarith

end Aux_PBstep

open ProphetBipartite Aux_PBstep in
theorem solution {L R : Type*} [Fintype L] [Fintype R]
    (M Q : L → R → ℝ) (hM : ∀ i j, 0 ≤ M i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hcol : ∀ j, ∑ i, Q i j ≤ 1)
    (l : L → ℝ) (r : R → ℝ) :
    error17 M Q (algorithm1Step M Q (l, r)).1 (algorithm1Step M Q (l, r)).2 ≤
        (3 / 4) * error17 M Q l r ∧
      ∀ t : ℕ, error17 M Q ((algorithm1Step M Q)^[t] (l, r)).1
          ((algorithm1Step M Q)^[t] (l, r)).2 ≤
        (3 / 4) ^ t * error17 M Q l r := by
  have hstep : ∀ p : (L → ℝ) × (R → ℝ),
      error17 M Q (algorithm1Step M Q p).1 (algorithm1Step M Q p).2 ≤
        (3 / 4) * error17 M Q p.1 p.2 := by
    rintro ⟨a, b⟩
    exact step_le M Q hQ hrow hcol a b
  refine ⟨step_le M Q hQ hrow hcol l r, ?_⟩
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc error17 M Q (algorithm1Step M Q ((algorithm1Step M Q)^[n] (l, r))).1
          (algorithm1Step M Q ((algorithm1Step M Q)^[n] (l, r))).2
        ≤ (3 / 4) * error17 M Q ((algorithm1Step M Q)^[n] (l, r)).1
          ((algorithm1Step M Q)^[n] (l, r)).2 := hstep _
      _ ≤ (3 / 4) * ((3 / 4) ^ n * error17 M Q l r) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (3 / 4) ^ (n + 1) * error17 M Q l r := by ring
