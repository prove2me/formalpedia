-- Prove2me | solution 1 for PrimePairSieve.reciprocal_batch_certificate_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:14:51.567984+00:00
-- url     : https://prove2.me/submissions/5c9adc17-c136-4040-9843-5b1be42eb635

import Definitions.Def_PrimePairSieve_ReciprocalBatch
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
set_option autoImplicit false

namespace ReciprocalRoundedCertificate

/-- Integer division rounds each nonnegative contribution down. -/
theorem rounded_term (scale L n numerator denominator : ℕ)
    (hscale : 0 < scale) (hL : 0 < L) (hd : 0 < denominator) :
    ((scale * numerator * L / (denominator * (L+n)) : ℕ) : ℝ) / scale ≤
      ((numerator : ℝ) / denominator) / (1 + (n : ℝ) / L) := by
  have hround := Nat.div_mul_le_self (scale * numerator * L) (denominator * (L+n))
  have hroundR :
      (((scale * numerator * L / (denominator * (L+n)) : ℕ) : ℝ)) *
        ((denominator : ℝ) * (L+n)) ≤ (scale : ℝ) * numerator * L := by
    exact_mod_cast hround
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have hden : (0 : ℝ) < denominator := by exact_mod_cast hd
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have heq : ((numerator : ℝ) / denominator) / (1 + (n : ℝ) / L) =
      (numerator : ℝ) * L / ((denominator : ℝ) * (L+n)) := by
    field_simp
  rw [heq]
  apply (div_le_div_iff₀ hs (by positivity)).mpr
  nlinarith [hroundR]

/-- A selected finite subset and integer-rounded sums certify the endpoint sum.
The subset prevents double counting; nonnegativity permits omitted coefficients. -/
theorem endpoint_lower (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (s : Finset ℕ) (L scale : ℕ) (hL : 0 < L) (hscale : 0 < scale)
    (numerator denominator : ℕ → ℕ)
    (hsubset : s ⊆ Finset.Icc 1 L)
    (hden : ∀ n ∈ s, 0 < denominator n)
    (hweight : ∀ n ∈ s, c n = (numerator n : ℝ) / denominator n) :
    ((∑ n ∈ s, scale * numerator n * L / (denominator n * (L+n)) : ℕ) : ℝ) / scale ≤
      ∑ n ∈ Finset.Icc 1 L, c n / (1 + (n : ℝ) / L) := by
  rw [Nat.cast_sum, Finset.sum_div]
  calc
    _ ≤ ∑ n ∈ s, c n / (1 + (n : ℝ) / L) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [hweight n hn]
      exact rounded_term scale L n (numerator n) (denominator n) hscale hL (hden n hn)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun n _ _ => div_nonneg (hc n) (by positivity))

#print axioms rounded_term
#print axioms endpoint_lower
end ReciprocalRoundedCertificate
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

lemma rows_lower (scale L : ℕ) (hs : 0 < scale) (hL : 0 < L)
    (rows : List Row) (hnodup : (rows.map Row.n).Nodup)
    (hrows : ∀ r ∈ rows, rowCheck r = true) :
    (((rows.map (rounded scale L)).sum : ℕ) : ℝ)/scale ≤
      ∑ n ∈ (rows.map Row.n).toFinset,
        weight n/(1+(n:ℝ)/L) := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    have hd := List.nodup_cons.mp hnodup
    have hr := row_sound r (hrows r (by simp))
    have ht := ih hd.2 (fun s hs => hrows s (by simp [hs]))
    have hterm := ReciprocalRoundedCertificate.rounded_term scale L r.n r.a r.b hs hL hr.1
    rw [← hr.2.2] at hterm
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hd.1)]
    exact add_le_add hterm ht

lemma endpoint_lower (scale L : ℕ) (hs : 0 < scale) (hL : 0 < L)
    (rows : List Row) (hchain : (rows.map Row.n).IsChain (· < ·))
    (hrows : rows.all rowCheck = true) :
    (roundedSum scale L rows : ℝ)/scale ≤
      ∑ n ∈ Finset.Icc 1 L,
        weight n/(1+(n:ℝ)/L) := by
  have hgood : ∀ r ∈ rows, rowCheck r = true := List.all_eq_true.mp hrows
  have hnd : (rows.map Row.n).Nodup := (List.isChain_iff_pairwise.mp hchain).nodup
  have hsub : ((rows.filter (fun r => r.n ≤ L)).map Row.n).Sublist (rows.map Row.n) :=
    (List.filter_sublist).map Row.n
  have h := rows_lower scale L hs hL (rows.filter (fun r => r.n ≤ L))
    (hnd.sublist hsub) (fun r hr => hgood r (List.mem_filter.mp hr).1)
  apply h.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hn
    obtain ⟨r,⟨hr,hrL⟩,rfl⟩ := hn
    exact Finset.mem_Icc.mpr ⟨(row_sound r (hgood r hr)).2.1,hrL⟩
  · intro n _ _
    exact div_nonneg (nonneg n) (by positivity)

end PrimePairSieve.ReciprocalBatch
theorem solution (scale L : ℕ) (hs : 0 < scale) (hL : 0 < L)
    (rows : List PrimePairSieve.ReciprocalBatch.Row)
    (hchain : (rows.map PrimePairSieve.ReciprocalBatch.Row.n).IsChain (· < ·))
    (hrows : rows.all PrimePairSieve.ReciprocalBatch.rowCheck = true) :
    (PrimePairSieve.ReciprocalBatch.roundedSum scale L rows : ℝ)/scale ≤
      ∑ n ∈ Finset.Icc 1 L,
        (if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/L) := by
  exact PrimePairSieve.ReciprocalBatch.endpoint_lower scale L hs hL rows hchain hrows

#print axioms solution
