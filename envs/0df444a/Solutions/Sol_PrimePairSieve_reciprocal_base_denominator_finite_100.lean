-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_finite_100
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:36:21.271029+00:00
-- url     : https://prove2.me/submissions/7e14f413-8866-4a9c-a4a3-51c2c9317d24

import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Analysis.Complex.ExponentialBounds

import Mathlib.Data.Nat.Squarefree

import Mathlib.Tactic

import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_interval_certificate

open scoped BigOperators

set_option autoImplicit false

set_option maxHeartbeats 10000000

set_option maxRecDepth 10000


open scoped BigOperators
set_option autoImplicit false

namespace ReciprocalWeightCertificate
noncomputable section

/-- Check a finite prime-factor set by primality and its exact natural product. -/
def check (n : ℕ) (s : Finset ℕ) : Bool :=
  decide ((∀ p ∈ s, Nat.Prime p) ∧ (∏ p ∈ s, p) = n)

/-- A factor-set certificate proves squarefreeness and the exact factor set. -/
theorem sound (n : ℕ) (s : Finset ℕ) (hcheck : check n s = true) :
    Squarefree n ∧ n.primeFactors = s := by
  have hv : (∀ p ∈ s, Nat.Prime p) ∧ (∏ p ∈ s, p) = n := of_decide_eq_true hcheck
  rcases hv with ⟨hs, hprod⟩
  subst n
  have hsf : Squarefree (∏ p ∈ s, p) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      (fun p hp => (hs p hp).squarefree)
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq
  exact ⟨hsf, Nat.primeFactors_prod hs⟩

/-- The certificate yields exactly the literal public reciprocal sieve weight. -/
theorem weight_eq (n : ℕ) (s : Finset ℕ) (hcheck : check n s = true) :
    (if Squarefree n then
      ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2/((p : ℝ)-2) else 0) =
    ∏ p ∈ s, if p = 2 then (1 : ℝ) else 2/((p : ℝ)-2) := by
  rcases sound n s hcheck with ⟨hsf,hfactors⟩
  rw [if_pos hsf, hfactors]

/-- Pure rational arithmetic on a checked factor set matches the real weight. -/
theorem weight_eq_rational (n : ℕ) (s : Finset ℕ) (hcheck : check n s = true) :
    (if Squarefree n then
      ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2/((p : ℝ)-2) else 0) =
    ((∏ p ∈ s, if p = 2 then (1 : ℚ) else 2/((p : ℚ)-2) : ℚ) : ℝ) := by
  rw [weight_eq n s hcheck]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  split_ifs <;> push_cast <;> rfl

example : check 30 {2,3,5} = true := by decide +kernel
example : check 1 ∅ = true := by decide +kernel
example : check 12 {2,3} = false := by decide +kernel

example :
    (if Squarefree (30 : ℕ) then
      ∏ p ∈ (30 : ℕ).primeFactors, if p = 2 then (1 : ℝ) else 2/((p : ℝ)-2) else 0) =
    4/3 := by
  rw [weight_eq 30 {2,3,5} (by decide +kernel)]
  norm_num

#print axioms sound
#print axioms weight_eq
#print axioms weight_eq_rational
end
end ReciprocalWeightCertificate


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

namespace ReciprocalPilot

noncomputable section

def c (n : ℕ) : ℝ := if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then 1 else 2/((p:ℝ)-2) else 0

lemma nonneg (n : ℕ) : 0 ≤ c n := by
  unfold c
  split_ifs
  · apply Finset.prod_nonneg
    intro p hp
    split_ifs with hp2
    · norm_num
    · have h3 : 3 ≤ p := by
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
      have h3R : (3:ℝ) ≤ p := by exact_mod_cast h3
      exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl

def selected : Finset ℕ := {1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,26,29,30,31,33,34,35,37,38,39,41,42,43,46,47,51,53,55,57,58,59,61,62,65,66,67,69,70,71,73,74,77,78,79,82,83,85,86,87,89,91,93,94,95,97}

def numerator (n : ℕ) : ℕ := match n with
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 10 => 2
  | 11 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 4
  | 17 => 2
  | 19 => 2
  | 21 => 4
  | 22 => 2
  | 23 => 2
  | 26 => 2
  | 29 => 2
  | 30 => 4
  | 31 => 2
  | 33 => 4
  | 34 => 2
  | 35 => 4
  | 37 => 2
  | 38 => 2
  | 39 => 4
  | 41 => 2
  | 42 => 4
  | 43 => 2
  | 46 => 2
  | 47 => 2
  | 51 => 4
  | 53 => 2
  | 55 => 4
  | 57 => 4
  | 58 => 2
  | 59 => 2
  | 61 => 2
  | 62 => 2
  | 65 => 4
  | 66 => 4
  | 67 => 2
  | 69 => 4
  | 70 => 4
  | 71 => 2
  | 73 => 2
  | 74 => 2
  | 77 => 4
  | 78 => 4
  | 79 => 2
  | 82 => 2
  | 83 => 2
  | 85 => 4
  | 86 => 2
  | 87 => 4
  | 89 => 2
  | 91 => 4
  | 93 => 4
  | 94 => 2
  | 95 => 4
  | 97 => 2
  | _ => 0

def denominator (n : ℕ) : ℕ := match n with
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 5 => 3
  | 6 => 1
  | 7 => 5
  | 10 => 3
  | 11 => 9
  | 13 => 11
  | 14 => 5
  | 15 => 3
  | 17 => 15
  | 19 => 17
  | 21 => 5
  | 22 => 9
  | 23 => 21
  | 26 => 11
  | 29 => 27
  | 30 => 3
  | 31 => 29
  | 33 => 9
  | 34 => 15
  | 35 => 15
  | 37 => 35
  | 38 => 17
  | 39 => 11
  | 41 => 39
  | 42 => 5
  | 43 => 41
  | 46 => 21
  | 47 => 45
  | 51 => 15
  | 53 => 51
  | 55 => 27
  | 57 => 17
  | 58 => 27
  | 59 => 57
  | 61 => 59
  | 62 => 29
  | 65 => 33
  | 66 => 9
  | 67 => 65
  | 69 => 21
  | 70 => 15
  | 71 => 69
  | 73 => 71
  | 74 => 35
  | 77 => 45
  | 78 => 11
  | 79 => 77
  | 82 => 39
  | 83 => 81
  | 85 => 45
  | 86 => 41
  | 87 => 27
  | 89 => 87
  | 91 => 55
  | 93 => 29
  | 94 => 45
  | 95 => 51
  | 97 => 95
  | _ => 1

lemma weight_1 : c 1 = (1:ℝ)/1 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 1 ∅ (by decide +kernel)]
  norm_num

lemma weight_2 : c 2 = (1:ℝ)/1 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 2 {2} (by decide +kernel)]
  norm_num

lemma weight_3 : c 3 = (2:ℝ)/1 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 3 {3} (by decide +kernel)]
  norm_num

lemma weight_5 : c 5 = (2:ℝ)/3 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 5 {5} (by decide +kernel)]
  norm_num

lemma weight_6 : c 6 = (2:ℝ)/1 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 6 {2,3} (by decide +kernel)]
  norm_num

lemma weight_7 : c 7 = (2:ℝ)/5 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 7 {7} (by decide +kernel)]
  norm_num

lemma weight_10 : c 10 = (2:ℝ)/3 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 10 {2,5} (by decide +kernel)]
  norm_num

lemma weight_11 : c 11 = (2:ℝ)/9 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 11 {11} (by decide +kernel)]
  norm_num

lemma weight_13 : c 13 = (2:ℝ)/11 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 13 {13} (by decide +kernel)]
  norm_num

lemma weight_14 : c 14 = (2:ℝ)/5 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 14 {2,7} (by decide +kernel)]
  norm_num

lemma weight_15 : c 15 = (4:ℝ)/3 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 15 {3,5} (by decide +kernel)]
  norm_num

lemma weight_17 : c 17 = (2:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 17 {17} (by decide +kernel)]
  norm_num

lemma weight_19 : c 19 = (2:ℝ)/17 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 19 {19} (by decide +kernel)]
  norm_num

lemma weight_21 : c 21 = (4:ℝ)/5 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 21 {3,7} (by decide +kernel)]
  norm_num

lemma weight_22 : c 22 = (2:ℝ)/9 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 22 {2,11} (by decide +kernel)]
  norm_num

lemma weight_23 : c 23 = (2:ℝ)/21 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 23 {23} (by decide +kernel)]
  norm_num

lemma weight_26 : c 26 = (2:ℝ)/11 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 26 {2,13} (by decide +kernel)]
  norm_num

lemma weight_29 : c 29 = (2:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 29 {29} (by decide +kernel)]
  norm_num

lemma weight_30 : c 30 = (4:ℝ)/3 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 30 {2,3,5} (by decide +kernel)]
  norm_num

lemma weight_31 : c 31 = (2:ℝ)/29 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 31 {31} (by decide +kernel)]
  norm_num

lemma weight_33 : c 33 = (4:ℝ)/9 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 33 {3,11} (by decide +kernel)]
  norm_num

lemma weight_34 : c 34 = (2:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 34 {2,17} (by decide +kernel)]
  norm_num

lemma weight_35 : c 35 = (4:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 35 {5,7} (by decide +kernel)]
  norm_num

lemma weight_37 : c 37 = (2:ℝ)/35 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 37 {37} (by decide +kernel)]
  norm_num

lemma weight_38 : c 38 = (2:ℝ)/17 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 38 {2,19} (by decide +kernel)]
  norm_num

lemma weight_39 : c 39 = (4:ℝ)/11 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 39 {3,13} (by decide +kernel)]
  norm_num

lemma weight_41 : c 41 = (2:ℝ)/39 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 41 {41} (by decide +kernel)]
  norm_num

lemma weight_42 : c 42 = (4:ℝ)/5 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 42 {2,3,7} (by decide +kernel)]
  norm_num

lemma weight_43 : c 43 = (2:ℝ)/41 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 43 {43} (by decide +kernel)]
  norm_num

lemma weight_46 : c 46 = (2:ℝ)/21 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 46 {2,23} (by decide +kernel)]
  norm_num

lemma weight_47 : c 47 = (2:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 47 {47} (by decide +kernel)]
  norm_num

lemma weight_51 : c 51 = (4:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 51 {3,17} (by decide +kernel)]
  norm_num

lemma weight_53 : c 53 = (2:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 53 {53} (by decide +kernel)]
  norm_num

lemma weight_55 : c 55 = (4:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 55 {5,11} (by decide +kernel)]
  norm_num

lemma weight_57 : c 57 = (4:ℝ)/17 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 57 {3,19} (by decide +kernel)]
  norm_num

lemma weight_58 : c 58 = (2:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 58 {2,29} (by decide +kernel)]
  norm_num

lemma weight_59 : c 59 = (2:ℝ)/57 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 59 {59} (by decide +kernel)]
  norm_num

lemma weight_61 : c 61 = (2:ℝ)/59 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 61 {61} (by decide +kernel)]
  norm_num

lemma weight_62 : c 62 = (2:ℝ)/29 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 62 {2,31} (by decide +kernel)]
  norm_num

lemma weight_65 : c 65 = (4:ℝ)/33 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 65 {5,13} (by decide +kernel)]
  norm_num

lemma weight_66 : c 66 = (4:ℝ)/9 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 66 {2,3,11} (by decide +kernel)]
  norm_num

lemma weight_67 : c 67 = (2:ℝ)/65 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 67 {67} (by decide +kernel)]
  norm_num

lemma weight_69 : c 69 = (4:ℝ)/21 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 69 {3,23} (by decide +kernel)]
  norm_num

lemma weight_70 : c 70 = (4:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 70 {2,5,7} (by decide +kernel)]
  norm_num

lemma weight_71 : c 71 = (2:ℝ)/69 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 71 {71} (by decide +kernel)]
  norm_num

lemma weight_73 : c 73 = (2:ℝ)/71 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 73 {73} (by decide +kernel)]
  norm_num

lemma weight_74 : c 74 = (2:ℝ)/35 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 74 {2,37} (by decide +kernel)]
  norm_num

lemma weight_77 : c 77 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 77 {7,11} (by decide +kernel)]
  norm_num

lemma weight_78 : c 78 = (4:ℝ)/11 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 78 {2,3,13} (by decide +kernel)]
  norm_num

lemma weight_79 : c 79 = (2:ℝ)/77 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 79 {79} (by decide +kernel)]
  norm_num

lemma weight_82 : c 82 = (2:ℝ)/39 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 82 {2,41} (by decide +kernel)]
  norm_num

lemma weight_83 : c 83 = (2:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 83 {83} (by decide +kernel)]
  norm_num

lemma weight_85 : c 85 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 85 {5,17} (by decide +kernel)]
  norm_num

lemma weight_86 : c 86 = (2:ℝ)/41 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 86 {2,43} (by decide +kernel)]
  norm_num

lemma weight_87 : c 87 = (4:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 87 {3,29} (by decide +kernel)]
  norm_num

lemma weight_89 : c 89 = (2:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 89 {89} (by decide +kernel)]
  norm_num

lemma weight_91 : c 91 = (4:ℝ)/55 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 91 {7,13} (by decide +kernel)]
  norm_num

lemma weight_93 : c 93 = (4:ℝ)/29 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 93 {3,31} (by decide +kernel)]
  norm_num

lemma weight_94 : c 94 = (2:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 94 {2,47} (by decide +kernel)]
  norm_num

lemma weight_95 : c 95 = (4:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 95 {5,19} (by decide +kernel)]
  norm_num

lemma weight_97 : c 97 = (2:ℝ)/95 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 97 {97} (by decide +kernel)]
  norm_num

lemma weights (n : ℕ) (hn : n ∈ selected) : c n = (numerator n : ℝ)/denominator n := by
  simp only [selected, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [numerator, denominator] using weight_1
  · simpa [numerator, denominator] using weight_2
  · simpa [numerator, denominator] using weight_3
  · simpa [numerator, denominator] using weight_5
  · simpa [numerator, denominator] using weight_6
  · simpa [numerator, denominator] using weight_7
  · simpa [numerator, denominator] using weight_10
  · simpa [numerator, denominator] using weight_11
  · simpa [numerator, denominator] using weight_13
  · simpa [numerator, denominator] using weight_14
  · simpa [numerator, denominator] using weight_15
  · simpa [numerator, denominator] using weight_17
  · simpa [numerator, denominator] using weight_19
  · simpa [numerator, denominator] using weight_21
  · simpa [numerator, denominator] using weight_22
  · simpa [numerator, denominator] using weight_23
  · simpa [numerator, denominator] using weight_26
  · simpa [numerator, denominator] using weight_29
  · simpa [numerator, denominator] using weight_30
  · simpa [numerator, denominator] using weight_31
  · simpa [numerator, denominator] using weight_33
  · simpa [numerator, denominator] using weight_34
  · simpa [numerator, denominator] using weight_35
  · simpa [numerator, denominator] using weight_37
  · simpa [numerator, denominator] using weight_38
  · simpa [numerator, denominator] using weight_39
  · simpa [numerator, denominator] using weight_41
  · simpa [numerator, denominator] using weight_42
  · simpa [numerator, denominator] using weight_43
  · simpa [numerator, denominator] using weight_46
  · simpa [numerator, denominator] using weight_47
  · simpa [numerator, denominator] using weight_51
  · simpa [numerator, denominator] using weight_53
  · simpa [numerator, denominator] using weight_55
  · simpa [numerator, denominator] using weight_57
  · simpa [numerator, denominator] using weight_58
  · simpa [numerator, denominator] using weight_59
  · simpa [numerator, denominator] using weight_61
  · simpa [numerator, denominator] using weight_62
  · simpa [numerator, denominator] using weight_65
  · simpa [numerator, denominator] using weight_66
  · simpa [numerator, denominator] using weight_67
  · simpa [numerator, denominator] using weight_69
  · simpa [numerator, denominator] using weight_70
  · simpa [numerator, denominator] using weight_71
  · simpa [numerator, denominator] using weight_73
  · simpa [numerator, denominator] using weight_74
  · simpa [numerator, denominator] using weight_77
  · simpa [numerator, denominator] using weight_78
  · simpa [numerator, denominator] using weight_79
  · simpa [numerator, denominator] using weight_82
  · simpa [numerator, denominator] using weight_83
  · simpa [numerator, denominator] using weight_85
  · simpa [numerator, denominator] using weight_86
  · simpa [numerator, denominator] using weight_87
  · simpa [numerator, denominator] using weight_89
  · simpa [numerator, denominator] using weight_91
  · simpa [numerator, denominator] using weight_93
  · simpa [numerator, denominator] using weight_94
  · simpa [numerator, denominator] using weight_95
  · simpa [numerator, denominator] using weight_97


lemma denominator_pos (n : ℕ) : 0 < denominator n := by
  unfold denominator
  split <;> norm_num

lemma selected_positive : ∀ n ∈ selected, 1 ≤ n := by decide +kernel

def roundedSum (L : ℕ) : ℕ := ∑ n ∈ selected.filter (fun n => n ≤ L), 1000000 * numerator n * L / (denominator n * (L+n))

lemma lower (L : ℕ) (hL : 0 < L) : (roundedSum L : ℝ)/1000000 ≤
    ∑ n ∈ Finset.Icc 1 L, c n/(1+(n:ℝ)/L) := by
  apply ReciprocalRoundedCertificate.endpoint_lower c nonneg
    (selected.filter (fun n => n ≤ L)) L 1000000 hL (by norm_num) numerator denominator
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hs,hle⟩
    exact Finset.mem_Icc.mpr ⟨selected_positive n hs,hle⟩
  · intro n hn
    exact denominator_pos n
  · intro n hn
    exact weights n (Finset.mem_filter.mp hn).1

lemma log_46 : Real.log (4*(46:ℝ)) ≤ (652/125) := by
  have h := Real.log_div_le_sum_range_add (x := ((7/39):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (184:ℝ) = 7*Real.log 2 + Real.log ((23/16):ℝ) := by
    rw [show (184:ℝ) = 2^7*(23/16) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_40 (z : ℝ) (hl : 40 ≤ z) (hu : z ≤ 46) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 40 46 (652/125) z
    (by norm_num) hl hu log_46 (by norm_num)
  have hi : roundedSum 40 = 11159041 := by decide +kernel
  have hb := lower 40 (by norm_num)
  rw [hi] at hb
  have hr : ((652/125):ℝ)^2/(5/2)/(1-((40+1)/(16*40^2))*((652/125)^2/(5/2))) ≤ (11159041:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_56 : Real.log (4*(56:ℝ)) ≤ (1083/200) := by
  have h := Real.log_div_le_sum_range_add (x := ((3/11):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (224:ℝ) = 7*Real.log 2 + Real.log ((7/4):ℝ) := by
    rw [show (224:ℝ) = 2^7*(7/4) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_46 (z : ℝ) (hl : 46 ≤ z) (hu : z ≤ 56) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 46 56 (1083/200) z
    (by norm_num) hl hu log_56 (by norm_num)
  have hi : roundedSum 46 = 11964554 := by decide +kernel
  have hb := lower 46 (by norm_num)
  rw [hi] at hb
  have hr : ((1083/200):ℝ)^2/(5/2)/(1-((46+1)/(16*46^2))*((1083/200)^2/(5/2))) ≤ (11964554:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_66 : Real.log (4*(66:ℝ)) ≤ (697/125) := by
  have h := Real.log_div_le_sum_range_add (x := ((1/65):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (264:ℝ) = 8*Real.log 2 + Real.log ((33/32):ℝ) := by
    rw [show (264:ℝ) = 2^8*(33/32) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_56 (z : ℝ) (hl : 56 ≤ z) (hu : z ≤ 66) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 56 66 (697/125) z
    (by norm_num) hl hu log_66 (by norm_num)
  have hi : roundedSum 56 = 12646283 := by decide +kernel
  have hb := lower 56 (by norm_num)
  rw [hi] at hb
  have hr : ((697/125):ℝ)^2/(5/2)/(1-((56+1)/(16*56^2))*((697/125)^2/(5/2))) ≤ (12646283:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_80 : Real.log (4*(80:ℝ)) ≤ (5769/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((1/9):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (320:ℝ) = 8*Real.log 2 + Real.log ((5/4):ℝ) := by
    rw [show (320:ℝ) = 2^8*(5/4) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_66 (z : ℝ) (hl : 66 ≤ z) (hu : z ≤ 80) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 66 80 (5769/1000) z
    (by norm_num) hl hu log_80 (by norm_num)
  have hi : roundedSum 66 = 13512376 := by decide +kernel
  have hb := lower 66 (by norm_num)
  rw [hi] at hb
  have hr : ((5769/1000):ℝ)^2/(5/2)/(1-((66+1)/(16*66^2))*((5769/1000)^2/(5/2))) ≤ (13512376:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_99 : Real.log (4*(99:ℝ)) ≤ (5983/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((35/163):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (396:ℝ) = 8*Real.log 2 + Real.log ((99/64):ℝ) := by
    rw [show (396:ℝ) = 2^8*(99/64) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_80 (z : ℝ) (hl : 80 ≤ z) (hu : z ≤ 99) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 80 99 (5983/1000) z
    (by norm_num) hl hu log_99 (by norm_num)
  have hi : roundedSum 80 = 14494675 := by decide +kernel
  have hb := lower 80 (by norm_num)
  rw [hi] at hb
  have hr : ((5983/1000):ℝ)^2/(5/2)/(1-((80+1)/(16*80^2))*((5983/1000)^2/(5/2))) ≤ (14494675:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_100 : Real.log (4*(100:ℝ)) ≤ (5993/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((9/41):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (400:ℝ) = 8*Real.log 2 + Real.log ((25/16):ℝ) := by
    rw [show (400:ℝ) = 2^8*(25/16) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_99 (z : ℝ) (hl : 99 ≤ z) (hu : z ≤ 100) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 99 100 (5993/1000) z
    (by norm_num) hl hu log_100 (by norm_num)
  have hi : roundedSum 99 = 15359992 := by decide +kernel
  have hb := lower 99 (by norm_num)
  rw [hi] at hb
  have hr : ((5993/1000):ℝ)^2/(5/2)/(1-((99+1)/(16*99^2))*((5993/1000)^2/(5/2))) ≤ (15359992:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

end

end ReciprocalPilot

theorem solution (z : ℝ) (hz : 40 ≤ z) (hupper : z ≤ 100) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/z) := by

  by_cases h46 : z ≤ 46
  · exact ReciprocalPilot.cell_40 z (by linarith) h46

  by_cases h56 : z ≤ 56
  · exact ReciprocalPilot.cell_46 z (by linarith) h56

  by_cases h66 : z ≤ 66
  · exact ReciprocalPilot.cell_56 z (by linarith) h66

  by_cases h80 : z ≤ 80
  · exact ReciprocalPilot.cell_66 z (by linarith) h80

  by_cases h99 : z ≤ 99
  · exact ReciprocalPilot.cell_80 z (by linarith) h99

  exact ReciprocalPilot.cell_99 z (by linarith) hupper

#print axioms solution
