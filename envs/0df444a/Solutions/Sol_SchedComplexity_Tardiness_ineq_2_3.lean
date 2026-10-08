-- Prove2me | solution 1 for SchedComplexity.Tardiness.ineq_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:25:29.476086+00:00
-- url     : https://prove2.me/submissions/032b7667-ef7e-4eeb-886b-ba48219ebcfd

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Definitions.Def_SchedComplexity_Tardiness_Knapsack



namespace SchedComplexity.Tardiness

open Finset

lemma tard_S2 {m : ℕ} (T : Finset (Fin m)) (f : Fin m → ℤ) :
    2 * ∑ j ∈ T, ∑ k ∈ T.filter (· ≤ j), f j * f k
      = (∑ j ∈ T, f j) ^ 2 + ∑ j ∈ T, (f j) ^ 2 := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert μ s hlt ih =>
    have hμ : μ ∉ s := fun h => lt_irrefl _ (hlt μ h)
    rw [sum_insert hμ, sum_insert hμ, sum_insert hμ]
    have e1 : ∑ j ∈ s, ∑ k ∈ (insert μ s).filter (· ≤ j), f j * f k
        = ∑ j ∈ s, ∑ k ∈ s.filter (· ≤ j), f j * f k := by
      apply sum_congr rfl; intro j hj
      apply sum_congr _ (fun _ _ => rfl)
      ext k; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨h1 | h1, h2⟩
        · exfalso; subst h1; exact absurd (hlt j hj) (not_lt.mpr h2)
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
    have e2 : ∑ k ∈ (insert μ s).filter (· ≤ μ), f μ * f k
        = f μ * (∑ k ∈ s, f k) + f μ * f μ := by
      have : (insert μ s).filter (· ≤ μ) = insert μ s := by
        ext k; simp only [mem_filter, mem_insert]; constructor
        · exact fun h => h.1
        · intro h; refine ⟨h, ?_⟩
          rcases h with h | h
          · exact h ▸ le_rfl
          · exact (hlt k h).le
      rw [this, sum_insert hμ, ← mul_sum]; ring
    rw [e2, e1]
    linear_combination ih

lemma tard_swap {m : ℕ} (T : Finset (Fin m)) (G : Fin m → Fin m → ℤ) :
    ∑ j ∈ T, ∑ k ∈ T.filter (j ≤ ·), G j k = ∑ k ∈ T, ∑ j ∈ T.filter (· ≤ k), G j k := by
  apply Finset.sum_comm'
  intro x y; simp only [mem_filter]; tauto

lemma tard_cheb {m : ℕ} (g : Fin m → ℕ) (hmono : Monotone g) (r : ℕ)
    (hr : (univ.filter (fun k => g k ≠ 0)).card ≤ r) :
    2 * ∑ j : Fin m, ∑ k ∈ univ.filter (· ≤ j), (g k : ℤ) ≤ (r + 1) * ∑ k, (g k : ℤ) := by
  set s := univ.filter (fun k => g k ≠ 0) with hs
  set c := s.card with hc
  let w : Fin m → ℤ := fun k => ((univ.filter (k ≤ ·)).card : ℤ)
  have hX : ∑ j : Fin m, ∑ k ∈ univ.filter (· ≤ j), (g k : ℤ) = ∑ k, (g k : ℤ) * w k := by
    rw [Finset.sum_comm' (s := univ) (t := fun j => univ.filter (· ≤ j)) (t' := univ)
      (s' := fun k => univ.filter (k ≤ ·)) (by intro x y; simp)]
    apply sum_congr rfl; intro k _
    simp [w, mul_comm]
  have hXs : ∑ k, (g k : ℤ) * w k = ∑ k ∈ s, (g k : ℤ) * w k := by
    rw [hs, Finset.sum_filter]
    apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have hQs : ∑ k, (g k : ℤ) = ∑ k ∈ s, (g k : ℤ) := by
    rw [hs, Finset.sum_filter]
    apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have hwA : Antitone w := by
    intro x y hxy
    simp only [w]
    exact_mod_cast Finset.card_le_card (fun z hz => by
      simp only [mem_filter, mem_univ, true_and] at hz ⊢; exact le_trans hxy hz)
  have hch := (Monotone.antivary (f := fun k => (g k : ℤ)) (g := w)
      (fun x y h => Nat.cast_le.mpr (hmono h)) hwA).antivaryOn (s : Set (Fin m))
  have hch2 := hch.card_smul_sum_le_sum_smul_sum
  simp only [smul_eq_mul, nsmul_eq_mul] at hch2
  -- weights on s
  have hws : ∀ k ∈ s, w k = ((s.filter (k ≤ ·)).card : ℤ) := by
    intro k hk
    simp only [w]
    congr 1
    congr 1
    ext z; simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hz
      refine ⟨?_, hz⟩
      have hk' : g k ≠ 0 := (mem_filter.mp hk).2
      have := hmono hz
      simp only [hs, mem_filter, mem_univ, true_and]
      omega
    · exact fun h => h.2
  have hsw : 2 * ∑ k ∈ s, w k = (c : ℤ) ^ 2 + c := by
    have h1 := tard_S2 s (fun _ => (1:ℤ))
    have h3 := tard_swap s (fun _ _ => (1:ℤ))
    have h2 : ∑ k ∈ s, w k = ∑ j ∈ s, ∑ k ∈ s.filter (j ≤ ·), (1:ℤ) := by
      rw [sum_congr rfl hws]; simp
    rw [h2, h3]
    simpa [hc] using h1
  rw [hX, hXs, hQs]
  have hQ0 : (0:ℤ) ≤ ∑ k ∈ s, (g k : ℤ) := sum_nonneg (fun _ _ => by positivity)
  by_cases hc0 : c = 0
  · have : s = ∅ := Finset.card_eq_zero.mp hc0
    rw [this]; simp
  · have hcpos : (0:ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc0
    have hrr : (c:ℤ) ≤ r := by exact_mod_cast hr
    have : (c:ℤ) * (2 * ∑ k ∈ s, (g k : ℤ) * w k) ≤ (c:ℤ) * ((r + 1) * ∑ k ∈ s, (g k : ℤ)) := by
      rw [← hc] at hch2
      generalize ∑ k ∈ s, (g k : ℤ) * w k = X at *
      generalize ∑ k ∈ s, (g k : ℤ) = Q at *
      generalize ∑ k ∈ s, w k = W at *
      have h5 : 0 ≤ ((r:ℤ) - c) * c * Q := mul_nonneg (mul_nonneg (by linarith) hcpos.le) hQ0
      nlinarith [hch2, hsw, h5]
    exact le_of_mul_le_mul_left this hcpos


lemma tard_pos_split {t m : ℕ} (p : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) (k : ℕ) :
    posCompletion p π k = ∑ i : Fin t, (if i.val < k then p (π (Fin.castAdd m i)) else 0)
      + ∑ j : Fin m, (if t + j.val < k then p (π (Fin.natAdd t j)) else 0) := by
  unfold posCompletion
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

lemma tard_pos_head {t m : ℕ} (p : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) :
    posCompletion p π t = ∑ i : Fin t, p (π (Fin.castAdd m i)) := by
  rw [tard_pos_split]
  simp

lemma tard_tail_split {t m : ℕ} (p v : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) :
    tailWeighted p v π t = ∑ j : Fin m, (v (π (Fin.natAdd t j)) : ℤ) *
      ∑ k ∈ univ.filter (· ≤ j), (p (π (Fin.natAdd t k)) : ℤ) := by
  unfold tailWeighted
  rw [Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ i : Fin t, ¬ (t ≤ (Fin.castAdd m i).val) := by intro i; simp
  simp only [h0, if_false, sum_const_zero, zero_add]
  apply sum_congr rfl; intro j _
  have : t ≤ (Fin.natAdd t j).val := by simp
  rw [if_pos this]
  congr 1
  rw [tard_pos_split p π ((Fin.natAdd t j).val+1), tard_pos_head]
  simp
  have e1 : ∀ x : Fin t, (x.val ≤ t + j.val) := fun x => by have := x.isLt; omega
  simp only [e1, if_true]
  rw [Finset.sum_filter]; ring


lemma tard_pair_split {t m : ℕ} (F : Fin (t+m) → Fin (t+m) → ℤ) :
    ∑ i ∈ univ.filter (fun i : Fin (t+m) => t ≤ i.val), ∑ k ∈ univ.filter (fun k : Fin (t+m) => i ≤ k), F i k
      = ∑ j : Fin m, ∑ k ∈ univ.filter (j ≤ ·), F (Fin.natAdd t j) (Fin.natAdd t k) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ i : Fin t, ¬ (t ≤ (Fin.castAdd m i).val) := by intro i; simp
  simp only [h0, if_false, sum_const_zero, zero_add]
  apply sum_congr rfl; intro j _
  have : t ≤ (Fin.natAdd t j).val := by simp
  rw [if_pos this, Finset.sum_filter, Fin.sum_univ_add]
  have h1 : ∀ k : Fin t, ¬ (Fin.natAdd t j ≤ Fin.castAdd m k) := by
    intro k; simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd]; have := k.isLt; omega
  simp only [h1, if_false, sum_const_zero, zero_add]
  rw [Finset.sum_filter]
  apply sum_congr rfl; intro k _
  have e : (Fin.natAdd t j ≤ Fin.natAdd t k) ↔ j ≤ k := by
    simp only [Fin.le_def, Fin.val_natAdd]; omega
  simp only [e]

lemma tard_sum_aE {t : ℕ} (a : Fin t → ℕ) (b : ℕ) :
    ∑ j : Fin (t + tPrime a b), aExt a b j = bigA a := by
  rw [Fin.sum_univ_add]
  unfold bigA
  have h1 : ∀ i : Fin t, aExt a b (Fin.castAdd (tPrime a b) i) = a i := by
    intro i; simp [aExt]
  have h2 : ∀ j : Fin (tPrime a b), aExt a b (Fin.natAdd t j) = 0 := by
    intro j; simp [aExt]
  simp [h1, h2]

lemma tard_aExt_le {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (j : Fin (t + tPrime a b)) :
    aExt a b j ≤ aStar a := by
  unfold aExt aStar
  split_ifs with h
  · exact Finset.le_sup (f := a) (Finset.mem_univ _)
  · exact Nat.zero_le _

lemma tard_count_nonzero {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (univ.filter (fun k : Fin (tPrime a b) => aExt a b (π (Fin.natAdd t k)) ≠ 0)).card ≤ t := by
  have := Finset.card_le_card_of_injOn (s := univ.filter (fun k : Fin (tPrime a b) => aExt a b (π (Fin.natAdd t k)) ≠ 0))
    (t := Finset.range t) (fun k => (π (Fin.natAdd t k)).val) ?_ ?_
  · simpa using this
  · intro k hk
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
    simp only [coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    simp [aExt]
    intro h; omega
  · intro k _ k' _ h
    have := π.injective (Fin.ext h)
    simpa using this

lemma tard_cPi_eq {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    cPi a b τ π = (∑ i : Fin t, (aExt a b (π (Fin.castAdd (tPrime a b) i)) : ℤ)) - b := by
  unfold cPi
  rw [tard_pos_head]
  push_cast
  simp only [wtP, Nat.cast_add, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

lemma tard_head_tail {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (∑ i : Fin t, (aExt a b (π (Fin.castAdd (tPrime a b) i)) : ℤ)) +
      ∑ j : Fin (tPrime a b), (aExt a b (π (Fin.natAdd t j)) : ℤ) = bigA a := by
  have h := tard_sum_aE a b
  have h2 : ∑ j : Fin (t + tPrime a b), (aExt a b (π j) : ℤ) = bigA a := by
    rw [Equiv.sum_comp π (fun j => (aExt a b j : ℤ))]
    exact_mod_cast h
  rw [← h2, Fin.sum_univ_add]

lemma tard_g_bounds {m : ℕ} (g : Fin m → ℕ) (B t : ℕ) (hle : ∀ j, g j ≤ B)
    (hc : (univ.filter (fun k => g k ≠ 0)).card ≤ t) :
    ((∑ j, (g j : ℤ)) ^ 2 + ∑ j, (g j : ℤ) ^ 2) ≤ (t : ℤ) * (t + 1) * (B : ℤ) ^ 2 := by
  set s := univ.filter (fun k => g k ≠ 0) with hs
  have e1 : ∑ j, (g j : ℤ) = ∑ j ∈ s, (g j : ℤ) := by
    rw [hs, Finset.sum_filter]; apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have e2 : ∑ j, (g j : ℤ) ^ 2 = ∑ j ∈ s, (g j : ℤ) ^ 2 := by
    rw [hs, Finset.sum_filter]; apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have b1 : ∑ j ∈ s, (g j : ℤ) ≤ s.card * B := by
    calc ∑ j ∈ s, (g j : ℤ) ≤ ∑ j ∈ s, (B : ℤ) := sum_le_sum (fun j _ => by exact_mod_cast hle j)
      _ = s.card * B := by simp
  have b2 : ∑ j ∈ s, (g j : ℤ) ^ 2 ≤ s.card * (B : ℤ) ^ 2 := by
    calc ∑ j ∈ s, (g j : ℤ) ^ 2 ≤ ∑ j ∈ s, (B : ℤ) ^ 2 :=
          sum_le_sum (fun j _ => pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle j) 2)
      _ = s.card * (B : ℤ) ^ 2 := by simp
  have q0 : (0:ℤ) ≤ ∑ j ∈ s, (g j : ℤ) := sum_nonneg (fun _ _ => by positivity)
  have hct : (s.card : ℤ) ≤ t := by exact_mod_cast hc
  rw [e1, e2]
  have h3 : (∑ j ∈ s, (g j : ℤ)) ^ 2 ≤ ((s.card : ℤ) * B) ^ 2 := pow_le_pow_left₀ q0 b1 2
  have hB : (0:ℤ) ≤ (B:ℤ)^2 := by positivity
  have hc0 : (0:ℤ) ≤ s.card := by positivity
  nlinarith [mul_nonneg hB (mul_nonneg hc0 (sub_nonneg.mpr hct)), mul_nonneg hB (sub_nonneg.mpr hct)]

lemma tard_S2' {m : ℕ} (T : Finset (Fin m)) (f : Fin m → ℤ) :
    2 * ∑ j ∈ T, ∑ k ∈ T.filter (j ≤ ·), f j * f k
      = (∑ j ∈ T, f j) ^ 2 + ∑ j ∈ T, (f j) ^ 2 := by
  rw [tard_swap T (fun j k => f j * f k), ← tard_S2 T f]
  congr 1
  apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; ring

/-- tail values of the job indices -/
def tailG {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    Fin (tPrime a b) → ℕ := fun j => aExt a b (π (Fin.natAdd t j))

lemma tard_wtP_tail {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b)))
    (j : Fin (tPrime a b)) :
    ((wtP a b τ (π (Fin.natAdd t j)) : ℕ) : ℤ) = τ + (tailG a b π j : ℤ) := by
  simp [wtP, tailG]

lemma tard_aPS {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    2 * aPairSum a b π = (∑ j, (tailG a b π j : ℤ)) ^ 2 + ∑ j, (tailG a b π j : ℤ) ^ 2 := by
  have hAP : aPairSum a b π = ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (j ≤ ·),
      (tailG a b π j : ℤ) * tailG a b π k := by
    unfold aPairSum
    exact tard_pair_split (fun i k => (aExt a b (π i) : ℤ) * aExt a b (π k))
  rw [hAP]
  exact tard_S2' univ (fun j => (tailG a b π j : ℤ))

lemma tard_tailpp {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    2 * tailWeighted (wtP a b τ) (wtP a b τ) π t =
      (tPrime a b : ℤ) * (tPrime a b + 1) * τ ^ 2 +
      2 * (tPrime a b + 1) * τ * (∑ j, (tailG a b π j : ℤ)) + 2 * aPairSum a b π := by
  have e : tailWeighted (wtP a b τ) (wtP a b τ) π t = ∑ j : Fin (tPrime a b),
      ∑ k ∈ univ.filter (· ≤ j), ((τ : ℤ) + tailG a b π j) * ((τ : ℤ) + tailG a b π k) := by
    rw [tard_tail_split]
    simp only [tard_wtP_tail, mul_sum]
  rw [e, tard_aPS]
  have hf := tard_S2 univ (fun j => (τ : ℤ) + (tailG a b π j : ℤ))
  beta_reduce at hf
  rw [hf]
  have s1 : ∑ j : Fin (tPrime a b), ((τ : ℤ) + (tailG a b π j : ℤ)) =
      tPrime a b * τ + ∑ j, (tailG a b π j : ℤ) := by
    rw [sum_add_distrib]; simp
  have s2 : ∑ j : Fin (tPrime a b), ((τ : ℤ) + (tailG a b π j : ℤ)) ^ 2 =
      tPrime a b * τ ^ 2 + 2 * τ * ∑ j, (tailG a b π j : ℤ) + ∑ j, (tailG a b π j : ℤ) ^ 2 := by
    have : ∀ j, ((τ : ℤ) + (tailG a b π j : ℤ)) ^ 2
        = τ ^ 2 + 2 * τ * (tailG a b π j : ℤ) + (tailG a b π j : ℤ) ^ 2 := fun j => by ring
    simp only [this, sum_add_distrib, ← mul_sum]
    simp
  rw [s1, s2]; ring

lemma tard_tail1 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ N Y : ℤ, 2 * N = (tPrime a b : ℤ) ^ 2 + tPrime a b ∧
      Y = ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (tailG a b π k : ℤ) ∧
      tailWeighted (wtP a b τ) (fun _ => 1) π t = τ * N + Y := by
  refine ⟨∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (1 : ℤ),
    ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (tailG a b π k : ℤ), ?_, rfl, ?_⟩
  · have := tard_S2 (Finset.univ : Finset (Fin (tPrime a b))) (fun _ => (1 : ℤ))
    simpa using this
  · rw [tard_tail_split]
    simp only [tard_wtP_tail, Nat.cast_one, one_mul, mul_sum, sum_add_distrib, sum_const]
    congr 1
    apply sum_congr rfl; intro x _; simp [mul_comm]

lemma tard_Q {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∑ j, (tailG a b π j : ℤ) = (bigA a : ℤ) - b - cPi a b τ π := by
  have h := tard_head_tail a b π
  rw [tard_cPi_eq]
  unfold tailG
  linarith

lemma tard_yThr2 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (hbA : b < bigA a) :
    2 * (yThr a b τ : ℤ) = (tPrime a b : ℤ) * (tPrime a b + 1) * τ * (τ + 1)
      + 2 * (tPrime a b + 1) * τ * ((bigA a : ℤ) - b) + 2 * tPrime a b := by
  unfold yThr
  have hd : 2 ∣ tPrime a b * (tPrime a b + 1) * τ * (τ + 1) := by
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self (tPrime a b)
    exact ⟨k * τ * (τ + 1), by rw [hk]; ring⟩
  obtain ⟨k, hk⟩ := hd
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
  have h1 : (((bigA a - b : ℕ)) : ℤ) = (bigA a : ℤ) - b := by
    rw [Nat.cast_sub hbA.le]
  have hk' : (tPrime a b : ℤ) * (tPrime a b + 1) * τ * (τ + 1) = 2 * k := by exact_mod_cast hk
  push_cast
  rw [h1]
  linear_combination (-1 : ℤ) * hk'

lemma tard_tPrime_ge {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (hbA : b < bigA a) :
    ((t : ℤ) + 1) * ((bigA a : ℤ) - b) + t * (t + 1) * (aStar a : ℤ) ^ 2 ≤ 2 * tPrime a b := by
  unfold tPrime
  have h1 : (((bigA a - b : ℕ)) : ℤ) = (bigA a : ℤ) - b := by
    rw [Nat.cast_sub hbA.le]
  rw [← h1]
  have : (((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2 : ℕ) * 2 + 1 ≥
      (t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1 := by omega
  have h2 : (((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 : ℕ) : ℤ) ≤
      2 * ((((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2 : ℕ) : ℤ) := by
    have : (t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 ≤
      2 * (((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2) := by omega
    exact_mod_cast this
  push_cast at h2
  exact h2


lemma tard_tail_wtW {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtW a b τ) π t =
      tailWeighted (wtP a b τ) (wtP a b τ) π t + tailWeighted (wtP a b τ) (fun _ => 1) π t := by
  rw [tard_tail_split, tard_tail_split, tard_tail_split, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  have : ((wtW a b τ (π (Fin.natAdd t j)) : ℕ) : ℤ) =
      ((wtP a b τ (π (Fin.natAdd t j)) : ℕ) : ℤ) + 1 := by simp [wtW, wtP]
  rw [this]; push_cast; ring

lemma tard_aPS_nonneg {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    0 ≤ aPairSum a b π := by
  have h := tard_aPS a b π
  have h2 : (0:ℤ) ≤ ∑ j, (tailG a b π j : ℤ) ^ 2 := sum_nonneg (fun j _ => sq_nonneg _)
  nlinarith [sq_nonneg (∑ j, (tailG a b π j : ℤ))]

lemma tard_aPS_le {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    2 * aPairSum a b π ≤ (t : ℤ) * (t + 1) * (aStar a : ℤ) ^ 2 := by
  rw [tard_aPS]
  exact tard_g_bounds (tailG a b π) (aStar a) t (fun j => tard_aExt_le a b _)
    (tard_count_nonzero a b π)

lemma tard_Y_nonneg {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    0 ≤ ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (tailG a b π k : ℤ) :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))

lemma tard_ineq6 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (hbA : b < bigA a)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (yThr a b τ : ℤ) - (tPrime a b + 1) * τ * cPi a b τ π - tPrime a b ≤
      tailWeighted (wtP a b τ) (wtW a b τ) π t := by
  rw [tard_tail_wtW]
  have h1 := tard_tailpp a b τ π
  obtain ⟨N, Y, hN, hY, hT⟩ := tard_tail1 a b τ π
  have hy := tard_yThr2 a b τ hbA
  have hQ := tard_Q a b τ π
  have hY0 : 0 ≤ Y := by rw [hY]; exact tard_Y_nonneg a b π
  have hP := tard_aPS_nonneg a b π
  rw [hT]
  rw [hQ] at h1
  have hτN : 2 * ((τ : ℤ) * N) = τ * ((tPrime a b : ℤ) ^ 2 + tPrime a b) := by
    linear_combination (τ : ℤ) * hN
  nlinarith [h1, hy, hτN, hY0, hP]

lemma tard_sorted_exists {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧ Monotone (tailG a b π') := by
  let τ' := Tuple.sort (tailG a b π)
  have hmono : Monotone (tailG a b π ∘ τ') := Tuple.monotone_sort (tailG a b π)
  let σ : Equiv.Perm (Fin (t + tPrime a b)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin t)) τ').trans finSumFinEquiv)
  have hσc : ∀ i : Fin t, σ (Fin.castAdd (tPrime a b) i) = Fin.castAdd (tPrime a b) i := by
    intro i; simp [σ]
  have hσn : ∀ j : Fin (tPrime a b), σ (Fin.natAdd t j) = Fin.natAdd t (τ' j) := by
    intro j; simp [σ]
  refine ⟨σ.trans π, ?_, ?_⟩
  · intro i hi
    obtain ⟨x, rfl⟩ : ∃ x : Fin t, i = Fin.castAdd (tPrime a b) x := ⟨⟨i.val, hi⟩, by ext; simp⟩
    show π (σ _) = π _
    rw [hσc]
  · intro x y hxy
    have := hmono hxy
    simpa [tailG, hσn] using this

lemma tard_cPi_congr {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π π' : Equiv.Perm (Fin (t + tPrime a b)))
    (h : ∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) :
    cPi a b τ π' = cPi a b τ π := by
  rw [tard_cPi_eq, tard_cPi_eq]
  congr 1
  apply sum_congr rfl; intro i _
  rw [h]; simp


lemma tard_ineq5 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      2 * tailWeighted (wtP a b τ) (fun _ => 1) π' t ≤
        (tPrime a b : ℤ) * (tPrime a b + 1) * τ
          + ((t : ℤ) + 1) * ((bigA a : ℤ) - b - cPi a b τ π) := by
  obtain ⟨π', hsame, hmono⟩ := tard_sorted_exists a b π
  refine ⟨π', hsame, ?_⟩
  obtain ⟨N, Y, hN, hY, hT⟩ := tard_tail1 a b τ π'
  have hc := tard_cheb (tailG a b π') hmono t (tard_count_nonzero a b π')
  have hQ := tard_Q a b τ π'
  rw [tard_cPi_congr a b τ π π' hsame] at hQ
  rw [hQ] at hc
  rw [← hY] at hc
  have hτN : 2 * ((τ : ℤ) * N) = τ * ((tPrime a b : ℤ) ^ 2 + tPrime a b) := by
    linear_combination (τ : ℤ) * hN
  rw [hT]
  nlinarith [hc, hτN]

lemma tard_ineq7 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (hbA : b < bigA a)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      2 * tailWeighted (wtP a b τ) (wtW a b τ) π' t ≤
        2 * (yThr a b τ : ℤ) - 2 * (tPrime a b + 1) * τ * cPi a b τ π
          - ((t : ℤ) + 1) * cPi a b τ π := by
  obtain ⟨π', hsame, h5⟩ := tard_ineq5 a b τ π
  refine ⟨π', hsame, ?_⟩
  rw [tard_tail_wtW]
  have h1 := tard_tailpp a b τ π'
  have hQ := tard_Q a b τ π'
  rw [tard_cPi_congr a b τ π π' hsame] at hQ
  rw [hQ] at h1
  have h3 := tard_aPS_le a b π'
  have hy := tard_yThr2 a b τ hbA
  have hp := tard_tPrime_ge a b hbA
  nlinarith [h1, h5, h3, hy, hp]

theorem ineq_2_3_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtP a b τ) π t =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (t + tPrime a b) => t ≤ i.val),
          ∑ k ∈ Finset.univ.filter (fun k : Fin (t + tPrime a b) => i ≤ k),
            (wtP a b τ (π i) : ℤ) * wtP a b τ (π k) ∧
    (tailWeighted (wtP a b τ) (wtP a b τ) π t : ℝ) =
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * (τ : ℝ) ^ 2
          + (tPrime a b + 1) * (τ : ℝ) * ((bigA a : ℝ) - b - cPi a b τ π)
          + aPairSum a b π ∧
    0 ≤ aPairSum a b π ∧
    (aPairSum a b π : ℝ) ≤ (1 / 2 : ℝ) * t * (t + 1) * (aStar a : ℝ) ^ 2 := by
  refine ⟨?_, ?_, tard_aPS_nonneg a b π, ?_⟩
  · rw [tard_pair_split (fun i k => (wtP a b τ (π i) : ℤ) * wtP a b τ (π k))]
    have e : tailWeighted (wtP a b τ) (wtP a b τ) π t = ∑ j : Fin (tPrime a b),
        ∑ k ∈ univ.filter (· ≤ j), ((τ : ℤ) + tailG a b π j) * ((τ : ℤ) + tailG a b π k) := by
      rw [tard_tail_split]
      simp only [tard_wtP_tail, mul_sum]
    rw [e]
    simp only [tard_wtP_tail]
    rw [tard_swap univ (fun j k => ((τ : ℤ) + tailG a b π j) * ((τ : ℤ) + tailG a b π k))]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro k _
    ring
  · have h1 := tard_tailpp a b τ π
    rw [tard_Q a b τ π] at h1
    have h1r : ((2 * tailWeighted (wtP a b τ) (wtP a b τ) π t : ℤ) : ℝ) =
        (((tPrime a b : ℤ) * (tPrime a b + 1) * τ ^ 2 +
        2 * (tPrime a b + 1) * τ * ((bigA a : ℤ) - b - cPi a b τ π) + 2 * aPairSum a b π : ℤ) : ℝ) := by
      rw [h1]
    push_cast at h1r
    linarith
  · have h3 := tard_aPS_le a b π
    have h3r : ((2 * aPairSum a b π : ℤ) : ℝ) ≤ (((t : ℤ) * (t + 1) * (aStar a : ℤ) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h3r
    linarith

theorem ineq_4_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ ≤
      (tailWeighted (wtP a b τ) (fun _ => 1) π t : ℝ) := by
  obtain ⟨N, Y, hN, hY, hT⟩ := tard_tail1 a b τ π
  have hY0 : 0 ≤ Y := by rw [hY]; exact tard_Y_nonneg a b π
  have h2N : (2 : ℝ) * N = (tPrime a b : ℝ) ^ 2 + tPrime a b := by exact_mod_cast hN
  have hTr : (tailWeighted (wtP a b τ) (fun _ => 1) π t : ℝ) = τ * N + Y := by
    rw [hT]; push_cast; ring
  have hY0r : (0 : ℝ) ≤ Y := by exact_mod_cast hY0
  rw [hTr]
  have key : (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ = τ * N := by
    linear_combination (-(τ : ℝ) / 2) * h2N
  linarith

theorem ineq_5_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      (tailWeighted (wtP a b τ) (fun _ => 1) π' t : ℝ) ≤
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ
          + (1 / 2 : ℝ) * (t + 1) * ((bigA a : ℝ) - b - cPi a b τ π) := by
  obtain ⟨π', hs, h⟩ := tard_ineq5 a b τ π
  refine ⟨π', hs, ?_⟩
  have hr : ((2 * tailWeighted (wtP a b τ) (fun _ => 1) π' t : ℤ) : ℝ) ≤
      (((tPrime a b : ℤ) * (tPrime a b + 1) * τ
          + ((t : ℤ) + 1) * ((bigA a : ℤ) - b - cPi a b τ π) : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at hr
  linarith

theorem ineq_6_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (yThr a b τ : ℝ) - (tPrime a b + 1) * (τ : ℝ) * cPi a b τ π - tPrime a b ≤
      (tailWeighted (wtP a b τ) (wtW a b τ) π t : ℝ) := by
  have h := tard_ineq6 a b τ hbA π
  have hr : (((yThr a b τ : ℤ) - (tPrime a b + 1) * τ * cPi a b τ π - tPrime a b : ℤ) : ℝ) ≤
      ((tailWeighted (wtP a b τ) (wtW a b τ) π t : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  exact hr

theorem ineq_7_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      (tailWeighted (wtP a b τ) (wtW a b τ) π' t : ℝ) ≤
        (yThr a b τ : ℝ) - (tPrime a b + 1) * (τ : ℝ) * cPi a b τ π
          - (1 / 2 : ℝ) * (t + 1) * cPi a b τ π := by
  obtain ⟨π', hs, h⟩ := tard_ineq7 a b τ hbA π
  refine ⟨π', hs, ?_⟩
  have hr : ((2 * tailWeighted (wtP a b τ) (wtW a b τ) π' t : ℤ) : ℝ) ≤
      ((2 * (yThr a b τ : ℤ) - 2 * (tPrime a b + 1) * τ * cPi a b τ π
          - ((t : ℤ) + 1) * cPi a b τ π : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at hr
  linarith


end SchedComplexity.Tardiness

open SchedComplexity.Tardiness


theorem solution {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtP a b τ) π t =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (t + tPrime a b) => t ≤ i.val),
          ∑ k ∈ Finset.univ.filter (fun k : Fin (t + tPrime a b) => i ≤ k),
            (wtP a b τ (π i) : ℤ) * wtP a b τ (π k) ∧
    (tailWeighted (wtP a b τ) (wtP a b τ) π t : ℝ) =
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * (τ : ℝ) ^ 2
          + (tPrime a b + 1) * (τ : ℝ) * ((bigA a : ℝ) - b - cPi a b τ π)
          + aPairSum a b π ∧
    0 ≤ aPairSum a b π ∧
    (aPairSum a b π : ℝ) ≤ (1 / 2 : ℝ) * t * (t + 1) * (aStar a : ℝ) ^ 2 := by
  exact ineq_2_3_core a b τ ha hb hbA hτ π
