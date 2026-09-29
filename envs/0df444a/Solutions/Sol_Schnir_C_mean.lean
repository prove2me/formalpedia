-- Prove2me | solution 1 for Schnir.C_mean
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T22:52:11.828996+00:00
-- url     : https://prove2.me/submissions/a15a8a9b-ecb0-4011-ab13-d97ef39c9886

import Mathlib
import Definitions.Def_Schnir_defs

open Finset Real

namespace Schnir

noncomputable def cmean_b (p : ℕ) : ℝ := ((1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 2 - 1) / p

lemma cmean_b_nonneg (p : ℕ) : 0 ≤ cmean_b p := by
  unfold cmean_b
  apply div_nonneg _ (Nat.cast_nonneg _)
  have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
  nlinarith

lemma cmean_b_le (p : ℕ) (hp : 11 ≤ p) :
    cmean_b p ≤ 211 / 100 * (1 / ((p : ℝ) - 1) ^ 2) := by
  unfold cmean_b
  have h : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := (p : ℝ) - 1 with hqdef
  have hpq : (p : ℝ) = q + 1 := by rw [hqdef]; ring
  rw [hpq]
  have hq10 : (10 : ℝ) ≤ q := by linarith
  rw [div_le_iff₀ (by linarith)]
  have e : (1 + (q + 1) / q ^ 2) ^ 2 - 1 = (2 * (q + 1) * q ^ 2 + (q + 1) ^ 2) / q ^ 4 := by
    field_simp; ring
  rw [e, show 211 / 100 * (1 / q ^ 2) * (q + 1) = (211 / 100 * (q + 1) * q ^ 2) / q ^ 4 by
    field_simp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

lemma cmean_tail (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Odd p ∧ 11 ≤ p) :
    ∀ m : ℕ, 9 ≤ m → (∀ p ∈ Q, p ≤ m) →
      ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 18 - 1 / (2 * (m : ℝ)) := by
  induction Q using Finset.induction_on_max with
  | empty =>
    intro m hm _
    have : (9 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [sum_empty]
    rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  | insert a s hlt ih =>
    intro m hm hle
    have ha := hQ a (mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert has]
    have ih' := ih (fun p hp => hQ p (mem_insert_of_mem hp)) (a - 2) (by omega) (by
      intro p hp
      have h1 := hlt p hp
      have h2 := (hQ p (mem_insert_of_mem hp)).1
      obtain ⟨k, hk⟩ := h2
      obtain ⟨j, hj⟩ := ha.1
      omega)
    have hcast : ((a - 2 : ℕ) : ℝ) = (a : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast] at ih'
    have haR : (11 : ℝ) ≤ a := by exact_mod_cast ha.2
    have hma : (a : ℝ) ≤ m := by exact_mod_cast hle a (mem_insert_self a s)
    have key : 1 / ((a : ℝ) - 1) ^ 2 ≤ 1 / (2 * ((a : ℝ) - 2)) - 1 / (2 * (a : ℝ)) := by
      rw [div_sub_div _ _ (by nlinarith) (by nlinarith), div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    have hm2 : 1 / (2 * (m : ℝ)) ≤ 1 / (2 * (a : ℝ)) := by
      apply one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith

lemma cmean_exp_le (t : ℝ) (ht : t < 1) : exp t ≤ 1 / (1 - t) := by
  have h := Real.add_one_le_exp (-t)
  rw [le_div_iff₀ (by linarith)]
  have : exp t * exp (-t) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t]

lemma cmean_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) :
    ∏ p ∈ P, (1 + cmean_b p) ≤ 7 / 3 := by
  set Q := P.filter (fun p => 11 ≤ p) with hQdef
  have hsub : P ⊆ ({3, 5, 7} : Finset ℕ) ∪ Q := by
    intro p hp
    obtain ⟨hpr, hp2⟩ := hP p hp
    by_cases h : 11 ≤ p
    · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
    · apply mem_union_left
      have := hpr.two_le
      interval_cases p <;> first | (simp; done) | exact absurd rfl hp2 | norm_num at hpr
  have hdisj : Disjoint ({3, 5, 7} : Finset ℕ) Q := by
    rw [Finset.disjoint_left]
    intro a ha haQ
    have := (mem_filter.1 haQ).2
    simp at ha; omega
  have h1 : ∏ p ∈ P, (1 + cmean_b p) ≤ ∏ p ∈ ({3, 5, 7} : Finset ℕ) ∪ Q, (1 + cmean_b p) :=
    prod_le_prod_of_subset_of_one_le hsub (fun i _ => by linarith [cmean_b_nonneg i])
      (fun i _ _ => by linarith [cmean_b_nonneg i])
  rw [prod_union hdisj] at h1
  have h357 : ∏ p ∈ ({3, 5, 7} : Finset ℕ), (1 + cmean_b p) = 402875 / 196608 := by
    simp [cmean_b]; norm_num
  have hQodd : ∀ p ∈ Q, Odd p ∧ 11 ≤ p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨(hP p hp1).1.odd_of_ne_two (hP p hp1).2, hp2⟩
  have hsum : ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 18 := by
    have := cmean_tail Q hQodd (max 9 (Q.sup id)) (le_max_left _ _)
      (fun p hp => le_max_of_le_right (le_sup (f := id) hp))
    have h9 : (0 : ℝ) ≤ 1 / (2 * ((max 9 (Q.sup id) : ℕ) : ℝ)) := by positivity
    linarith
  have hbsum : ∑ p ∈ Q, cmean_b p ≤ 211 / 1800 := by
    calc ∑ p ∈ Q, cmean_b p ≤ ∑ p ∈ Q, 211 / 100 * (1 / ((p : ℝ) - 1) ^ 2) :=
          sum_le_sum (fun p hp => cmean_b_le p (hQodd p hp).2)
      _ = 211 / 100 * ∑ p ∈ Q, 1 / ((p : ℝ) - 1) ^ 2 := by rw [mul_sum]
      _ ≤ 211 / 100 * (1 / 18) := by gcongr
      _ = 211 / 1800 := by norm_num
  have hQprod : ∏ p ∈ Q, (1 + cmean_b p) ≤ 1 / (1 - 211 / 1800) := by
    calc ∏ p ∈ Q, (1 + cmean_b p) ≤ exp (∑ p ∈ Q, cmean_b p) :=
          Real.prod_one_add_le_exp_sum Q cmean_b_nonneg
      _ ≤ exp (211 / 1800) := exp_le_exp.2 hbsum
      _ ≤ 1 / (1 - 211 / 1800) := cmean_exp_le _ (by norm_num)
  rw [h357] at h1
  calc ∏ p ∈ P, (1 + cmean_b p) ≤ 402875 / 196608 * ∏ p ∈ Q, (1 + cmean_b p) := h1
    _ ≤ 402875 / 196608 * (1 / (1 - 211 / 1800)) := by gcongr
    _ ≤ 7 / 3 := by norm_num


lemma cmean_card (N : ℕ) (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ p ≠ 2) :
    (((Icc 1 N).filter Even).filter (fun s => ∀ p ∈ U, p ∣ s)).card
      ≤ N / (2 * ∏ p ∈ U, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card
  intro s hs
  simp only [mem_filter, mem_Icc, mem_Ioc] at hs ⊢
  obtain ⟨⟨⟨h1, h2⟩, hev⟩, hdiv⟩ := hs
  refine ⟨⟨by omega, h2⟩, ?_⟩
  have h2U : (2 : ℕ) ∉ U := fun h => (hU 2 h).2 rfl
  have : 2 * ∏ p ∈ U, p = ∏ p ∈ insert 2 U, p := by rw [prod_insert h2U]
  rw [this]
  apply Finset.prod_primes_dvd
  · intro a ha
    rw [mem_insert] at ha
    rcases ha with rfl | ha
    · exact Nat.prime_iff.1 Nat.prime_two
    · exact Nat.prime_iff.1 (hU a ha).1
  · intro a ha
    rw [mem_insert] at ha
    rcases ha with rfl | ha
    · exact even_iff_two_dvd.1 hev
    · exact hdiv a ha

lemma cmean_mul_b (p : ℕ) (hp : p ≠ 0) :
    (p : ℝ) * cmean_b p = (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ^ 2 - 1 := by
  unfold cmean_b
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp

lemma cmean_pointwise (N s : ℕ) (hs : s ∈ (Icc 1 N).filter Even) :
    C s ^ 2 = 9 * ∑ U ∈ ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)).powerset,
      if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * cmean_b p) else 0 := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2)
  simp only [mem_filter, mem_Icc] at hs
  obtain ⟨⟨h1, h2⟩, hev⟩ := hs
  have hs0 : s ≠ 0 := by omega
  have h2s : 2 ∈ s.primeFactors := by
    rw [Nat.mem_primeFactors]; exact ⟨Nat.prime_two, even_iff_two_dvd.1 hev, hs0⟩
  unfold C
  rw [← prod_pow, ← mul_prod_erase _ _ h2s]
  congr 1
  · norm_num
  simp_rw [← prod_ite_zero]
  rw [← prod_one_add]
  have hset : s.primeFactors.erase 2 = P.filter (fun p => p ∣ s) := by
    ext p
    simp only [mem_erase, Nat.mem_primeFactors, mem_filter, P, mem_range]
    constructor
    · rintro ⟨hp2, hpr, hdvd, -⟩
      exact ⟨⟨by have := Nat.le_of_dvd (by omega) hdvd; omega, hpr, hp2⟩, hdvd⟩
    · rintro ⟨⟨-, hpr, hp2⟩, hdvd⟩
      exact ⟨hp2, hpr, hdvd, hs0⟩
  rw [hset, prod_filter]
  apply prod_congr rfl
  intro p hp
  have hp0 : p ≠ 0 := (mem_filter.1 hp).2.1.ne_zero
  split_ifs
  · rw [cmean_mul_b p hp0]; ring
  · simp

/-- Note eq. (12): `∑_{s ≤ x, s even} C(s)^2 ≤ (21/2) x`. -/
theorem C_mean (x : ℝ) (hx : 0 ≤ x) :
    ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, (C s) ^ 2 ≤ 21 / 2 * x := by
  set N := ⌊x⌋₊
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hPdef
  have hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := fun p hp => (mem_filter.1 hp).2
  set E := (Icc 1 N).filter Even
  rw [sum_congr rfl (fun s hs => cmean_pointwise N s hs), ← mul_sum, sum_comm]
  have hterm : ∀ U ∈ P.powerset,
      ∑ s ∈ E, (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * cmean_b p) else 0)
        ≤ x / 2 * ∏ p ∈ U, cmean_b p := by
    intro U hU
    have hUP : ∀ p ∈ U, p.Prime ∧ p ≠ 2 := fun p hp => hP p (mem_powerset.1 hU hp)
    rw [← sum_filter, sum_const, nsmul_eq_mul, prod_mul_distrib]
    have hc := cmean_card N U hUP
    have hpos : (0 : ℝ) < ∏ p ∈ U, (p : ℝ) :=
      prod_pos (fun p hp => by exact_mod_cast (hUP p hp).1.pos)
    have hc' : ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) := by
      calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ)
          ≤ ((N / (2 * ∏ p ∈ U, p) : ℕ) : ℝ) := by exact_mod_cast hc
        _ ≤ (N : ℝ) / ((2 * ∏ p ∈ U, p : ℕ) : ℝ) := Nat.cast_div_le
        _ ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) := by
          push_cast
          gcongr
          exact Nat.floor_le hx
    have hb : 0 ≤ ∏ p ∈ U, cmean_b p := prod_nonneg (fun p _ => cmean_b_nonneg p)
    calc ((E.filter (fun s => ∀ p ∈ U, p ∣ s)).card : ℝ) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, cmean_b p)
        ≤ x / (2 * ∏ p ∈ U, (p : ℝ)) * ((∏ p ∈ U, (p : ℝ)) * ∏ p ∈ U, cmean_b p) := by
          gcongr
      _ = x / 2 * ∏ p ∈ U, cmean_b p := by field_simp
  calc 9 * ∑ U ∈ P.powerset, ∑ s ∈ E,
        (if (∀ p ∈ U, p ∣ s) then ∏ p ∈ U, ((p : ℝ) * cmean_b p) else 0)
      ≤ 9 * ∑ U ∈ P.powerset, x / 2 * ∏ p ∈ U, cmean_b p := by
        gcongr with U hU; exact hterm U hU
    _ = 9 * (x / 2) * ∏ p ∈ P, (1 + cmean_b p) := by
        rw [prod_one_add, mul_sum, mul_sum]; simp only [mul_assoc]
    _ ≤ 9 * (x / 2) * (7 / 3) := by gcongr; exact cmean_prod P hP
    _ = 21 / 2 * x := by ring

end Schnir

open Schnir in
theorem solution (x : ℝ) (hx : 0 ≤ x) :
    ∑ s ∈ (Finset.Icc 1 ⌊x⌋₊).filter Even, (C s) ^ 2 ≤ 21 / 2 * x :=
  Schnir.C_mean x hx
