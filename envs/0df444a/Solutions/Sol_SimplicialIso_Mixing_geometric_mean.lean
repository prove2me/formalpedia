-- Prove2me | solution 1 for SimplicialIso.Mixing.geometric_mean
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:02:32.543436+00:00
-- url     : https://prove2.me/submissions/880e08cd-adbc-4122-8bf9-76d0e3c68a29

import Mathlib

set_option autoImplicit false

open Finset
open scoped InnerProductSpace

lemma geo_perm_sum_eq {n : ℕ} (g : Fin (n + 1) → ℝ) (j k : Fin (n + 1)) :
    ∑ π : Equiv.Perm (Fin (n + 1)), g (π j) = ∑ π : Equiv.Perm (Fin (n + 1)), g (π k) := by
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k))]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp [Equiv.Perm.mul_apply]

lemma geo_perm_sum {n : ℕ} (g : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    ∑ π : Equiv.Perm (Fin (n + 1)), g (π j) = (n.factorial : ℝ) * ∑ i, g i := by
  have h1 : ∑ k : Fin (n + 1), ∑ π : Equiv.Perm (Fin (n + 1)), g (π k)
      = ((n + 1).factorial : ℝ) * ∑ i, g i := by
    rw [Finset.sum_comm]
    have : ∀ π : Equiv.Perm (Fin (n + 1)), ∑ k, g (π k) = ∑ i, g i :=
      fun π => Equiv.sum_comp π g
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
  have h2 : ∑ k : Fin (n + 1), ∑ π : Equiv.Perm (Fin (n + 1)), g (π k)
      = ((n : ℝ) + 1) * ∑ π : Equiv.Perm (Fin (n + 1)), g (π j) := by
    rw [Finset.sum_congr rfl fun k _ => geo_perm_sum_eq g k j]
    simp
  rw [h1, Nat.factorial_succ] at h2
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast at h2
  apply mul_left_cancel₀ hn
  rw [← h2]; ring

theorem solution (d : ℕ) (hd : 1 ≤ d) (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (x ρ : ℝ) (hx : 0 ≤ x)
    (h : ∀ π : Equiv.Perm (Fin (d + 1)),
      x ≤ ρ * Real.sqrt (a (π 0) * a (π (Fin.last d))) *
        ∏ i ∈ univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d), a (π i)) :
    x ≤ ρ * (∏ i, a i) ^ ((d : ℝ) / (d + 1)) := by
  have hexp : 0 < (d : ℝ) / (d + 1) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    have hP : ∏ i, a i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hP, Real.zero_rpow hexp.ne', mul_zero]
    -- permutation sending i to 0
    have := h (Equiv.swap i 0)
    have hmid : ∏ j ∈ univ.filter (fun j : Fin (d + 1) => j ≠ 0 ∧ j ≠ Fin.last d),
        a ((Equiv.swap i 0) j) = 0 ∨ a ((Equiv.swap i 0) 0) = 0 := by
      right; simp [hi]
    rcases hmid with hm | hm
    · rw [hm] at this; simpa using this
    · rw [hm] at this; simpa using this
  · push_neg at hz
    have hpos : ∀ i, 0 < a i := fun i => lt_of_le_of_ne (ha i) (Ne.symm (hz i))
    have hP : 0 < ∏ i, a i := Finset.prod_pos fun i _ => hpos i
    -- the bound
    set S : Equiv.Perm (Fin (d + 1)) → ℝ := fun π => Real.sqrt (a (π 0) * a (π (Fin.last d))) *
        ∏ i ∈ univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d), a (π i) with hS
    have hSpos : ∀ π, 0 < S π := by
      intro π
      refine mul_pos (Real.sqrt_pos.2 (mul_pos (hpos _) (hpos _))) ?_
      exact Finset.prod_pos fun i _ => hpos _
    have h' : ∀ π, x ≤ ρ * S π := fun π => by simpa [hS, mul_assoc] using h π
    have hρ : 0 ≤ ρ := by
      by_contra hneg
      push_neg at hneg
      have := h' 1
      have := mul_neg_of_neg_of_pos hneg (hSpos 1)
      linarith [h' 1]
    rcases hρ.eq_or_lt with hρ0 | hρpos
    · subst hρ0
      have := h' 1
      simp at this
      simp [this]
    rcases hx.eq_or_lt with hx0 | hxpos
    · rw [← hx0]; positivity
    -- logs
    have hlogS : ∀ π, Real.log (S π) = ∑ i, Real.log (a i)
        - (1/2) * Real.log (a (π 0)) - (1/2) * Real.log (a (π (Fin.last d))) := by
      intro π
      have hne : (0 : Fin (d + 1)) ≠ Fin.last d := by
        intro e
        have := congrArg Fin.val e
        simp at this; omega
      rw [hS]; dsimp only
      rw [Real.log_mul (Real.sqrt_pos.2 (mul_pos (hpos _) (hpos _))).ne'
        (Finset.prod_pos fun i _ => hpos _).ne', Real.log_sqrt (mul_pos (hpos _) (hpos _)).le,
        Real.log_mul (hpos _).ne' (hpos _).ne',
        Real.log_prod (fun i _ => (hpos _).ne')]
      -- sum over filter vs full
      have hsplit : ∑ i, Real.log (a (π i)) =
          ∑ i ∈ univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d), Real.log (a (π i))
          + Real.log (a (π 0)) + Real.log (a (π (Fin.last d))) := by
        have e : (univ : Finset (Fin (d + 1))) =
            insert 0 (insert (Fin.last d)
              (univ.filter (fun i : Fin (d + 1) => i ≠ 0 ∧ i ≠ Fin.last d))) := by
          ext i; simp only [mem_univ, mem_insert, mem_filter, true_and]; tauto
        conv_lhs => rw [e]
        rw [Finset.sum_insert, Finset.sum_insert]
        · ring
        · simp
        · simp [hne]
      have hperm : ∑ i, Real.log (a (π i)) = ∑ i, Real.log (a i) :=
        Equiv.sum_comp π (fun i => Real.log (a i))
      linarith
    have hlog : ∀ π, Real.log x ≤ Real.log ρ + Real.log (S π) := by
      intro π
      rw [← Real.log_mul hρpos.ne' (hSpos π).ne']
      exact Real.log_le_log hxpos (h' π)
    have hsum := Finset.sum_le_sum (s := univ) fun π _ => hlog π
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul, hlogS, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    rw [geo_perm_sum (fun i => Real.log (a i)) 0,
      geo_perm_sum (fun i => Real.log (a i)) (Fin.last d)] at hsum
    -- goal
    have hN : (0 : ℝ) < ((d + 1).factorial : ℝ) := by positivity
    have hf : (((d + 1).factorial : ℕ) : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfd : (0 : ℝ) < (d.factorial : ℝ) := by positivity
    rw [← Real.log_le_log_iff hxpos (by positivity),
      Real.log_mul hρpos.ne' (by positivity), Real.log_rpow hP, Real.log_prod (fun i _ => (hz i))]
    rw [hf] at hsum
    set L := ∑ i, Real.log (a i)
    have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have key : Real.log x * (((d : ℝ) + 1) * (d.factorial : ℝ)) ≤
        (Real.log ρ + (d : ℝ) / (d + 1) * L) * (((d : ℝ) + 1) * (d.factorial : ℝ)) := by
      have : (Real.log ρ + (d : ℝ) / (d + 1) * L) * (((d : ℝ) + 1) * (d.factorial : ℝ))
          = ((d : ℝ) + 1) * (d.factorial : ℝ) * Real.log ρ + (d : ℝ) * (d.factorial : ℝ) * L := by
        field_simp
      rw [this]
      nlinarith [hsum]
    exact le_of_mul_le_mul_right key (by positivity)
