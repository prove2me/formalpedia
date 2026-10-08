-- Prove2me | solution 1 for PrimePairSieve.reciprocal_mass_certificate_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:20:48.016164+00:00
-- url     : https://prove2.me/submissions/e9bbc692-de85-45e0-885d-20fe649c46c0

import Definitions.Def_PrimePairSieve_ReciprocalMass
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Tactic
open scoped BigOperators
set_option autoImplicit false
namespace PrimePairSieve.ReciprocalBatch

lemma row_sound (r : Row) (h : rowCheck r = true) :
    0 < r.b ∧ 0 < r.n ∧
    weight r.n = (r.a : ℝ)/r.b := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hc,ha⟩,hb⟩,hpos⟩
  refine ⟨hpos.1,hpos.2,?_⟩
  have hf : (∀ p ∈ r.factors, Nat.Prime p) ∧ (∏ p ∈ r.factors, p) = r.n :=
    hc
  have hsf : Squarefree r.n := by
    rw [← hf.2]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      (fun p hp => (hf.1 p hp).squarefree)
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hf.1 p hp) (hf.1 q hq)).mpr hpq
  have hfac : r.n.primeFactors = r.factors := by
    rw [← hf.2]
    exact Nat.primeFactors_prod hf.1
  rw [weight, if_pos hsf, hfac, ha, hb, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h2 : p = 2
  · simp [h2]
  · have hp2 := (hf.1 p hp).two_le
    simp [h2, Nat.cast_sub hp2]

lemma nonneg (n : ℕ) : 0 ≤ weight n := by
  unfold weight
  split_ifs
  · apply Finset.prod_nonneg
    intro p hp
    split_ifs with h2
    · norm_num
    · have h3 : 3 ≤ p := by
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
      have h3R : (3:ℝ) ≤ p := by exact_mod_cast h3
      exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

end PrimePairSieve.ReciprocalBatch
namespace PrimePairSieve.ReciprocalMass
open ReciprocalBatch
lemma term_lower (S a b : ℕ) (hS : 0 < S) (hb : 0 < b) :
    ((S * a / b : ℕ) : ℝ) / S ≤ (a : ℝ) / b := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hd : (0 : ℝ) < b := by exact_mod_cast hb
  have hround : (((S * a / b : ℕ) : ℝ)) * b ≤ (S : ℝ) * a := by
    exact_mod_cast Nat.div_mul_le_self (S * a) b
  apply (div_le_div_iff₀ hs hd).mpr
  nlinarith [hround]

lemma selected_lower (S : ℕ) (hS : 0 < S) (rows : List Row)
    (hnd : (rows.map Row.n).Nodup) (hrows : ∀ r ∈ rows, rowCheck r = true) :
    (((rows.map (fun r => S * r.a / r.b)).sum : ℕ) : ℝ) / S ≤
      ∑ n ∈ (rows.map Row.n).toFinset, weight n := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    have hd := List.nodup_cons.mp hnd
    have hr := row_sound r (hrows r (by simp))
    have ht := ih hd.2 (fun s hs => hrows s (by simp [hs]))
    have hterm := term_lower S r.a r.b hS hr.1
    rw [← hr.2.2] at hterm
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hd.1)]
    exact add_le_add hterm ht

theorem certificate (S A B : ℕ) (hS : 0 < S) (rows : List Row)
    (hchain : (rows.map Row.n).IsChain (· < ·))
    (hrows : rows.all rowCheck = true)
    (hbounds : rows.all (fun r => decide (A ≤ r.n ∧ r.n ≤ B)) = true) :
    (roundedMass S rows : ℝ) / S ≤ ∑ n ∈ Finset.Icc A B, weight n := by
  have hgood := List.all_eq_true.mp hrows
  have hbound := List.all_eq_true.mp hbounds
  have hnd : (rows.map Row.n).Nodup := (List.isChain_iff_pairwise.mp hchain).nodup
  have h := selected_lower S hS rows hnd hgood
  apply h.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨r, hr, rfl⟩ := hn
    exact Finset.mem_Icc.mpr (of_decide_eq_true (hbound r hr))
  · intro n _ _
    exact PrimePairSieve.ReciprocalBatch.nonneg n

end PrimePairSieve.ReciprocalMass
open PrimePairSieve

theorem solution (scale : ℕ) (hs : 0 < scale)
    (certs : List (ReciprocalMass.Bucket × List ReciprocalBatch.Row))
    (hrows : (certs.flatMap Prod.snd).all ReciprocalBatch.rowCheck = true)
    (hchecks : certs.all (ReciprocalMass.massCheck scale) = true) :
    ReciprocalMass.Valid scale (certs.map Prod.fst).toFinset := by
  intro b hb
  simp only [List.mem_toFinset, List.mem_map] at hb
  obtain ⟨cert, hc, rfl⟩ := hb
  have hcheck := List.all_eq_true.mp hchecks cert hc
  simp only [ReciprocalMass.massCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hr : cert.2.all ReciprocalBatch.rowCheck = true := by
    rw [List.all_eq_true]
    intro r hr
    exact List.all_eq_true.mp hrows r (List.mem_flatMap.mpr ⟨cert,hc,hr⟩)
  have h := ReciprocalMass.certificate scale cert.1.lower cert.1.upper hs cert.2
    hcheck.1.1 hr hcheck.1.2
  rw [hcheck.2] at h
  exact h
#print axioms solution
