-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_lemma14
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T08:57:36.691724+00:00
-- url     : https://prove2.me/submissions/a9f6ac54-422a-4f99-b0fd-1506c7affe93

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

namespace TaoFivePrimes

private lemma f_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b : ℝ) / ((b : ℝ) - 1) ≤ (a : ℝ) / ((a : ℝ) - 1) := by
  have ha' : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < (b : ℝ) - 1)
    (by linarith : (0 : ℝ) < (a : ℝ) - 1)]
  nlinarith

private lemma one_le_f {p : ℕ} (hp : p.Prime) : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
  linarith

private lemma nth_two_le (i : ℕ) : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
  have h2 : 2 ≤ Nat.nth Nat.Prime i := by
    have h := Nat.add_two_le_nth_prime i
    omega
  exact_mod_cast h2

private lemma prod_f_nonneg (m : ℕ) :
    (0 : ℝ) ≤ ∏ i ∈ Finset.range m, (Nat.nth Nat.Prime i : ℝ) :=
  le_trans zero_le_one (Finset.one_le_prod (fun i _ => by
    have h := nth_two_le i
    linarith))

private lemma prod_one_le_f (m : ℕ) :
    (1 : ℝ) ≤ ∏ i ∈ Finset.range m,
      (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) :=
  Finset.one_le_prod (fun i _ => one_le_f (Nat.prime_nth_prime i))

private lemma lemma14_comb : ∀ m : ℕ, ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) →
    (∏ p ∈ s, (p : ℝ)) < ∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ) →
    (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) ≤
      ∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := by
  intro m
  induction m with
  | zero =>
    intro s hs h
    have hs0 : s = ∅ := by
      by_contra hne
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hs p hp).two_le
      have hle : (p : ℝ) ≤ ∏ q ∈ s, (q : ℝ) := by
        have hsub : ({p} : Finset ℕ) ⊆ s := Finset.singleton_subset_iff.mpr hp
        have h' := Finset.prod_le_prod_of_subset_of_one_le
          (s := ({p} : Finset ℕ)) (t := s) (f := fun q : ℕ => (q : ℝ))
          hsub (fun i _ => by positivity)
          (fun i hi _ => by exact_mod_cast (hs i hi).one_le)
        simpa using h'
      have h2' : (2 : ℝ) ≤ ∏ q ∈ s, (q : ℝ) := h2.trans hle
      have hprod : ∏ i ∈ Finset.range (0 + 1), (Nat.nth Nat.Prime i : ℝ) = 2 := by
        rw [Finset.prod_range_one, Nat.nth_prime_zero_eq_two]
        norm_num
      rw [hprod] at h
      linarith
    rw [hs0]
    simp
  | succ m ih =>
    intro s hs h
    by_cases hne : s = ∅
    · rw [hne]
      simp only [Finset.prod_empty]
      exact prod_one_le_f (m + 1)
    · have hne' : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      set q := s.max' hne' with hq
      have hqmem : q ∈ s := s.max'_mem hne'
      have hqprime : Nat.Prime q := hs q hqmem
      have hs' : ∀ p ∈ s.erase q, Nat.Prime p := fun p hp => hs p (Finset.mem_of_mem_erase hp)
      have hqle : ∀ p ∈ s, p ≤ q := fun p hp => s.le_max' p hp
      have hsplit : (∏ p ∈ s, (p : ℝ)) = (q : ℝ) * ∏ p ∈ s.erase q, (p : ℝ) := by
        rw [← Finset.prod_erase_mul s (fun p => (p : ℝ)) hqmem, mul_comm]
      by_cases hcase : Nat.nth Nat.Prime (m + 1) ≤ q
      · have hpm1_le_q : (Nat.nth Nat.Prime (m + 1) : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast hcase
        have hpm_le_q : Nat.nth Nat.Prime m ≤ q :=
          le_trans ((Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (Nat.le_succ m)) hcase
        have hqpos : (0 : ℝ) < (q : ℝ) := by
          have h'' : (2 : ℝ) ≤ (q : ℝ) :=
            le_trans (nth_two_le (m + 1)) (by exact_mod_cast hcase)
          linarith
        have h1 : (q : ℝ) * ∏ p ∈ s.erase q, (p : ℝ) <
            (q : ℝ) * ∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ) := by
          calc (q : ℝ) * ∏ p ∈ s.erase q, (p : ℝ)
              = ∏ p ∈ s, (p : ℝ) := hsplit.symm
            _ < ∏ i ∈ Finset.range (m + 1 + 1), (Nat.nth Nat.Prime i : ℝ) := h
            _ = (∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ)) *
                  (Nat.nth Nat.Prime (m + 1) : ℝ) := Finset.prod_range_succ _ _
            _ ≤ (∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ)) * (q : ℝ) :=
                  mul_le_mul_of_nonneg_left hpm1_le_q (prod_f_nonneg (m + 1))
            _ = (q : ℝ) * ∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ) :=
                  mul_comm _ _
        have hlt' : ∏ p ∈ s.erase q, (p : ℝ) <
            ∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ) :=
          lt_of_mul_lt_mul_left h1 hqpos.le
        have ih' := ih (s.erase q) hs' hlt'
        have hsplitf : (∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)) =
            (∏ p ∈ s.erase q, (p : ℝ) / ((p : ℝ) - 1)) *
              ((q : ℝ) / ((q : ℝ) - 1)) := by
          rw [← Finset.prod_erase_mul s (fun p => (p : ℝ) / ((p : ℝ) - 1)) hqmem, mul_comm]
        rw [hsplitf, Finset.prod_range_succ]
        have hfq : (q : ℝ) / ((q : ℝ) - 1) ≤
            (Nat.nth Nat.Prime m : ℝ) / ((Nat.nth Nat.Prime m : ℝ) - 1) :=
          f_anti (by have h' := Nat.add_two_le_nth_prime m; omega) hpm_le_q
        exact mul_le_mul ih' hfq (le_trans zero_le_one (one_le_f hqprime))
          (le_trans zero_le_one (prod_one_le_f m))
      · have hq_lt : q < Nat.nth Nat.Prime (m + 1) := lt_of_not_ge hcase
        have hsub : s ⊆ (Finset.range (m + 1)).image (Nat.nth Nat.Prime) := by
          intro p hp
          rw [Finset.mem_image]
          have hpcount : Nat.count Nat.Prime p < m + 1 := by
            have h1 : Nat.count Nat.Prime p ≤ Nat.count Nat.Prime q :=
              Nat.count_monotone (p := Nat.Prime) (hqle p hp)
            have h2 : Nat.count Nat.Prime q <
                Nat.count Nat.Prime (Nat.nth Nat.Prime (m + 1)) :=
              Nat.count_strict_mono (p := Nat.Prime) hqprime hq_lt
            rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at h2
            omega
          exact ⟨Nat.count Nat.Prime p, by simpa using hpcount, Nat.nth_count (hs p hp)⟩
        have himg : ∏ x ∈ (Finset.range (m + 1)).image (Nat.nth Nat.Prime),
              (x : ℝ) / ((x : ℝ) - 1) =
            ∏ i ∈ Finset.range (m + 1),
              (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) :=
          Finset.prod_image
            (fun a _ b _ hab => Nat.nth_injective Nat.infinite_setOfPred_prime hab)
        calc ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1)
            ≤ ∏ x ∈ (Finset.range (m + 1)).image (Nat.nth Nat.Prime),
                (x : ℝ) / ((x : ℝ) - 1) :=
              Finset.prod_le_prod_of_subset_of_one_le hsub
                (fun i hi => le_trans zero_le_one (one_le_f (hs i hi)))
                (fun i hi _ => by
                  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
                  exact one_le_f (Nat.prime_nth_prime j))
          _ = ∏ i ∈ Finset.range (m + 1),
                (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := himg

private lemma primesLE_nth (m : ℕ) :
    Nat.primesLE (Nat.nth Nat.Prime m) =
      (Finset.range (m + 1)).image (Nat.nth Nat.Prime) := by
  ext p
  rw [Nat.mem_primesLE, Finset.mem_image]
  constructor
  · rintro ⟨hple, hpprime⟩
    refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hpprime⟩
    have hmono : Nat.count Nat.Prime p ≤ Nat.count Nat.Prime (Nat.nth Nat.Prime m) :=
      Nat.count_monotone (p := Nat.Prime) hple
    rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at hmono
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmono)
  · rintro ⟨i, hi, rfl⟩
    have him : i ≤ m := by simpa using hi
    exact ⟨(Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr him,
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i⟩

/-- Rosser–Schoenfeld (1962), Lemma 14: the primorial bound for `n/φ(n)`. -/
theorem solution (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m))) :
    (n : ℝ) / Nat.totient n ≤
      ∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := by
  have hnpos : 0 < n := by omega
  have hPcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, (p : ℝ) := by
    rw [Nat.cast_prod]
  have hQcast : ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl
      (fun p hp => Nat.cast_pred (Nat.prime_of_mem_primeFactors hp).pos)
  have hcast : (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have hh : (Nat.totient n : ℝ) * ↑(∏ p ∈ n.primeFactors, p) =
        (n : ℝ) * ↑(∏ p ∈ n.primeFactors, (p - 1)) := by
      exact_mod_cast Nat.totient_mul_prod_primeFactors n
    rwa [hPcast, hQcast] at hh
  have htot_ne : (Nat.totient n : ℝ) ≠ 0 := by
    have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr hnpos
    exact_mod_cast hpos.ne'
  have hQ_ne : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have hratio : (n : ℝ) / Nat.totient n =
      ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff htot_ne hQ_ne,
      mul_comm (∏ p ∈ n.primeFactors, (p : ℝ)) (Nat.totient n : ℝ)]
    exact hcast.symm
  have hexp : Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m)) =
      ∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, Real.exp_log]
    · rw [primorial_eq_prod_primesLE, primesLE_nth]
      push_cast
      rw [Finset.prod_image
        (fun a _ b _ hab => Nat.nth_injective Nat.infinite_setOfPred_prime hab)]
    · exact_mod_cast primorial_pos (Nat.nth Nat.Prime m)
  have hle_n : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ (n : ℝ) := by
    have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
    have hle : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hnpos hdvd
    calc ∏ p ∈ n.primeFactors, (p : ℝ) = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) :=
          hPcast.symm
      _ ≤ (n : ℝ) := by exact_mod_cast hle
  have hlt : (∏ p ∈ n.primeFactors, (p : ℝ)) <
      ∏ i ∈ Finset.range (m + 1), (Nat.nth Nat.Prime i : ℝ) := by
    rw [← hexp]
    exact lt_of_le_of_lt hle_n h
  calc (n : ℝ) / Nat.totient n
      = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := hratio
    _ ≤ ∏ i ∈ Finset.range m,
          (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) :=
        lemma14_comb m n.primeFactors
          (fun p hp => Nat.prime_of_mem_primeFactors hp) hlt

end TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m))) :
    (n : ℝ) / Nat.totient n ≤
      ∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) :=
  TaoFivePrimes.solution n m hn hm h
