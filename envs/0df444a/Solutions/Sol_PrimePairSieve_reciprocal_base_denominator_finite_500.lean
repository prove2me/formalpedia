-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_finite_500
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:33:40.737571+00:00
-- url     : https://prove2.me/submissions/e400f156-c8b0-44c8-8156-11a0bd1f47cb

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

def selected : Finset ℕ := {1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,26,29,30,31,33,34,35,37,38,39,41,42,43,46,47,51,53,55,57,58,59,61,62,65,66,69,70,74,77,78,82,85,86,87,91,93,94,95,102,105,106,110,111,114,115,118,119,122,123,129,130,133,138,141,143,145,154,155,159,161,165,170,174,177,182,183,185,186,190,195,201,205,210,213,219,222,230,231,237,238,246,249,255,258,266,267,273,282,285,286,290,291,303,309,310,318,321,322,327,330,339,345,354,357,366,370,385,390,399,402,410,426,429,435,438,455,462,465,474,483}

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
  | 69 => 4
  | 70 => 4
  | 74 => 2
  | 77 => 4
  | 78 => 4
  | 82 => 2
  | 85 => 4
  | 86 => 2
  | 87 => 4
  | 91 => 4
  | 93 => 4
  | 94 => 2
  | 95 => 4
  | 102 => 4
  | 105 => 8
  | 106 => 2
  | 110 => 4
  | 111 => 4
  | 114 => 4
  | 115 => 4
  | 118 => 2
  | 119 => 4
  | 122 => 2
  | 123 => 4
  | 129 => 4
  | 130 => 4
  | 133 => 4
  | 138 => 4
  | 141 => 4
  | 143 => 4
  | 145 => 4
  | 154 => 4
  | 155 => 4
  | 159 => 4
  | 161 => 4
  | 165 => 8
  | 170 => 4
  | 174 => 4
  | 177 => 4
  | 182 => 4
  | 183 => 4
  | 185 => 4
  | 186 => 4
  | 190 => 4
  | 195 => 8
  | 201 => 4
  | 205 => 4
  | 210 => 8
  | 213 => 4
  | 219 => 4
  | 222 => 4
  | 230 => 4
  | 231 => 8
  | 237 => 4
  | 238 => 4
  | 246 => 4
  | 249 => 4
  | 255 => 8
  | 258 => 4
  | 266 => 4
  | 267 => 4
  | 273 => 8
  | 282 => 4
  | 285 => 8
  | 286 => 4
  | 290 => 4
  | 291 => 4
  | 303 => 4
  | 309 => 4
  | 310 => 4
  | 318 => 4
  | 321 => 4
  | 322 => 4
  | 327 => 4
  | 330 => 8
  | 339 => 4
  | 345 => 8
  | 354 => 4
  | 357 => 8
  | 366 => 4
  | 370 => 4
  | 385 => 8
  | 390 => 8
  | 399 => 8
  | 402 => 4
  | 410 => 4
  | 426 => 4
  | 429 => 8
  | 435 => 8
  | 438 => 4
  | 455 => 8
  | 462 => 8
  | 465 => 8
  | 474 => 4
  | 483 => 8
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
  | 69 => 21
  | 70 => 15
  | 74 => 35
  | 77 => 45
  | 78 => 11
  | 82 => 39
  | 85 => 45
  | 86 => 41
  | 87 => 27
  | 91 => 55
  | 93 => 29
  | 94 => 45
  | 95 => 51
  | 102 => 15
  | 105 => 15
  | 106 => 51
  | 110 => 27
  | 111 => 35
  | 114 => 17
  | 115 => 63
  | 118 => 57
  | 119 => 75
  | 122 => 59
  | 123 => 39
  | 129 => 41
  | 130 => 33
  | 133 => 85
  | 138 => 21
  | 141 => 45
  | 143 => 99
  | 145 => 81
  | 154 => 45
  | 155 => 87
  | 159 => 51
  | 161 => 105
  | 165 => 27
  | 170 => 45
  | 174 => 27
  | 177 => 57
  | 182 => 55
  | 183 => 59
  | 185 => 105
  | 186 => 29
  | 190 => 51
  | 195 => 33
  | 201 => 65
  | 205 => 117
  | 210 => 15
  | 213 => 69
  | 219 => 71
  | 222 => 35
  | 230 => 63
  | 231 => 45
  | 237 => 77
  | 238 => 75
  | 246 => 39
  | 249 => 81
  | 255 => 45
  | 258 => 41
  | 266 => 85
  | 267 => 87
  | 273 => 55
  | 282 => 45
  | 285 => 51
  | 286 => 99
  | 290 => 81
  | 291 => 95
  | 303 => 99
  | 309 => 101
  | 310 => 87
  | 318 => 51
  | 321 => 105
  | 322 => 105
  | 327 => 107
  | 330 => 27
  | 339 => 111
  | 345 => 63
  | 354 => 57
  | 357 => 75
  | 366 => 59
  | 370 => 105
  | 385 => 135
  | 390 => 33
  | 399 => 85
  | 402 => 65
  | 410 => 117
  | 426 => 69
  | 429 => 99
  | 435 => 81
  | 438 => 71
  | 455 => 165
  | 462 => 45
  | 465 => 87
  | 474 => 77
  | 483 => 105
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

lemma weight_69 : c 69 = (4:ℝ)/21 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 69 {3,23} (by decide +kernel)]
  norm_num

lemma weight_70 : c 70 = (4:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 70 {2,5,7} (by decide +kernel)]
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

lemma weight_82 : c 82 = (2:ℝ)/39 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 82 {2,41} (by decide +kernel)]
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

lemma weight_102 : c 102 = (4:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 102 {2,3,17} (by decide +kernel)]
  norm_num

lemma weight_105 : c 105 = (8:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 105 {3,5,7} (by decide +kernel)]
  norm_num

lemma weight_106 : c 106 = (2:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 106 {2,53} (by decide +kernel)]
  norm_num

lemma weight_110 : c 110 = (4:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 110 {2,5,11} (by decide +kernel)]
  norm_num

lemma weight_111 : c 111 = (4:ℝ)/35 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 111 {3,37} (by decide +kernel)]
  norm_num

lemma weight_114 : c 114 = (4:ℝ)/17 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 114 {2,3,19} (by decide +kernel)]
  norm_num

lemma weight_115 : c 115 = (4:ℝ)/63 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 115 {5,23} (by decide +kernel)]
  norm_num

lemma weight_118 : c 118 = (2:ℝ)/57 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 118 {2,59} (by decide +kernel)]
  norm_num

lemma weight_119 : c 119 = (4:ℝ)/75 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 119 {7,17} (by decide +kernel)]
  norm_num

lemma weight_122 : c 122 = (2:ℝ)/59 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 122 {2,61} (by decide +kernel)]
  norm_num

lemma weight_123 : c 123 = (4:ℝ)/39 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 123 {3,41} (by decide +kernel)]
  norm_num

lemma weight_129 : c 129 = (4:ℝ)/41 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 129 {3,43} (by decide +kernel)]
  norm_num

lemma weight_130 : c 130 = (4:ℝ)/33 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 130 {2,5,13} (by decide +kernel)]
  norm_num

lemma weight_133 : c 133 = (4:ℝ)/85 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 133 {7,19} (by decide +kernel)]
  norm_num

lemma weight_138 : c 138 = (4:ℝ)/21 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 138 {2,3,23} (by decide +kernel)]
  norm_num

lemma weight_141 : c 141 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 141 {3,47} (by decide +kernel)]
  norm_num

lemma weight_143 : c 143 = (4:ℝ)/99 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 143 {11,13} (by decide +kernel)]
  norm_num

lemma weight_145 : c 145 = (4:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 145 {5,29} (by decide +kernel)]
  norm_num

lemma weight_154 : c 154 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 154 {2,7,11} (by decide +kernel)]
  norm_num

lemma weight_155 : c 155 = (4:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 155 {5,31} (by decide +kernel)]
  norm_num

lemma weight_159 : c 159 = (4:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 159 {3,53} (by decide +kernel)]
  norm_num

lemma weight_161 : c 161 = (4:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 161 {7,23} (by decide +kernel)]
  norm_num

lemma weight_165 : c 165 = (8:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 165 {3,5,11} (by decide +kernel)]
  norm_num

lemma weight_170 : c 170 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 170 {2,5,17} (by decide +kernel)]
  norm_num

lemma weight_174 : c 174 = (4:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 174 {2,3,29} (by decide +kernel)]
  norm_num

lemma weight_177 : c 177 = (4:ℝ)/57 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 177 {3,59} (by decide +kernel)]
  norm_num

lemma weight_182 : c 182 = (4:ℝ)/55 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 182 {2,7,13} (by decide +kernel)]
  norm_num

lemma weight_183 : c 183 = (4:ℝ)/59 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 183 {3,61} (by decide +kernel)]
  norm_num

lemma weight_185 : c 185 = (4:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 185 {5,37} (by decide +kernel)]
  norm_num

lemma weight_186 : c 186 = (4:ℝ)/29 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 186 {2,3,31} (by decide +kernel)]
  norm_num

lemma weight_190 : c 190 = (4:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 190 {2,5,19} (by decide +kernel)]
  norm_num

lemma weight_195 : c 195 = (8:ℝ)/33 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 195 {3,5,13} (by decide +kernel)]
  norm_num

lemma weight_201 : c 201 = (4:ℝ)/65 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 201 {3,67} (by decide +kernel)]
  norm_num

lemma weight_205 : c 205 = (4:ℝ)/117 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 205 {5,41} (by decide +kernel)]
  norm_num

lemma weight_210 : c 210 = (8:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 210 {2,3,5,7} (by decide +kernel)]
  norm_num

lemma weight_213 : c 213 = (4:ℝ)/69 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 213 {3,71} (by decide +kernel)]
  norm_num

lemma weight_219 : c 219 = (4:ℝ)/71 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 219 {3,73} (by decide +kernel)]
  norm_num

lemma weight_222 : c 222 = (4:ℝ)/35 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 222 {2,3,37} (by decide +kernel)]
  norm_num

lemma weight_230 : c 230 = (4:ℝ)/63 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 230 {2,5,23} (by decide +kernel)]
  norm_num

lemma weight_231 : c 231 = (8:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 231 {3,7,11} (by decide +kernel)]
  norm_num

lemma weight_237 : c 237 = (4:ℝ)/77 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 237 {3,79} (by decide +kernel)]
  norm_num

lemma weight_238 : c 238 = (4:ℝ)/75 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 238 {2,7,17} (by decide +kernel)]
  norm_num

lemma weight_246 : c 246 = (4:ℝ)/39 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 246 {2,3,41} (by decide +kernel)]
  norm_num

lemma weight_249 : c 249 = (4:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 249 {3,83} (by decide +kernel)]
  norm_num

lemma weight_255 : c 255 = (8:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 255 {3,5,17} (by decide +kernel)]
  norm_num

lemma weight_258 : c 258 = (4:ℝ)/41 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 258 {2,3,43} (by decide +kernel)]
  norm_num

lemma weight_266 : c 266 = (4:ℝ)/85 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 266 {2,7,19} (by decide +kernel)]
  norm_num

lemma weight_267 : c 267 = (4:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 267 {3,89} (by decide +kernel)]
  norm_num

lemma weight_273 : c 273 = (8:ℝ)/55 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 273 {3,7,13} (by decide +kernel)]
  norm_num

lemma weight_282 : c 282 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 282 {2,3,47} (by decide +kernel)]
  norm_num

lemma weight_285 : c 285 = (8:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 285 {3,5,19} (by decide +kernel)]
  norm_num

lemma weight_286 : c 286 = (4:ℝ)/99 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 286 {2,11,13} (by decide +kernel)]
  norm_num

lemma weight_290 : c 290 = (4:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 290 {2,5,29} (by decide +kernel)]
  norm_num

lemma weight_291 : c 291 = (4:ℝ)/95 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 291 {3,97} (by decide +kernel)]
  norm_num

lemma weight_303 : c 303 = (4:ℝ)/99 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 303 {3,101} (by decide +kernel)]
  norm_num

lemma weight_309 : c 309 = (4:ℝ)/101 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 309 {3,103} (by decide +kernel)]
  norm_num

lemma weight_310 : c 310 = (4:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 310 {2,5,31} (by decide +kernel)]
  norm_num

lemma weight_318 : c 318 = (4:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 318 {2,3,53} (by decide +kernel)]
  norm_num

lemma weight_321 : c 321 = (4:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 321 {3,107} (by decide +kernel)]
  norm_num

lemma weight_322 : c 322 = (4:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 322 {2,7,23} (by decide +kernel)]
  norm_num

lemma weight_327 : c 327 = (4:ℝ)/107 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 327 {3,109} (by decide +kernel)]
  norm_num

lemma weight_330 : c 330 = (8:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 330 {2,3,5,11} (by decide +kernel)]
  norm_num

lemma weight_339 : c 339 = (4:ℝ)/111 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 339 {3,113} (by decide +kernel)]
  norm_num

lemma weight_345 : c 345 = (8:ℝ)/63 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 345 {3,5,23} (by decide +kernel)]
  norm_num

lemma weight_354 : c 354 = (4:ℝ)/57 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 354 {2,3,59} (by decide +kernel)]
  norm_num

lemma weight_357 : c 357 = (8:ℝ)/75 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 357 {3,7,17} (by decide +kernel)]
  norm_num

lemma weight_366 : c 366 = (4:ℝ)/59 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 366 {2,3,61} (by decide +kernel)]
  norm_num

lemma weight_370 : c 370 = (4:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 370 {2,5,37} (by decide +kernel)]
  norm_num

lemma weight_385 : c 385 = (8:ℝ)/135 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 385 {5,7,11} (by decide +kernel)]
  norm_num

lemma weight_390 : c 390 = (8:ℝ)/33 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 390 {2,3,5,13} (by decide +kernel)]
  norm_num

lemma weight_399 : c 399 = (8:ℝ)/85 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 399 {3,7,19} (by decide +kernel)]
  norm_num

lemma weight_402 : c 402 = (4:ℝ)/65 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 402 {2,3,67} (by decide +kernel)]
  norm_num

lemma weight_410 : c 410 = (4:ℝ)/117 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 410 {2,5,41} (by decide +kernel)]
  norm_num

lemma weight_426 : c 426 = (4:ℝ)/69 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 426 {2,3,71} (by decide +kernel)]
  norm_num

lemma weight_429 : c 429 = (8:ℝ)/99 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 429 {3,11,13} (by decide +kernel)]
  norm_num

lemma weight_435 : c 435 = (8:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 435 {3,5,29} (by decide +kernel)]
  norm_num

lemma weight_438 : c 438 = (4:ℝ)/71 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 438 {2,3,73} (by decide +kernel)]
  norm_num

lemma weight_455 : c 455 = (8:ℝ)/165 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 455 {5,7,13} (by decide +kernel)]
  norm_num

lemma weight_462 : c 462 = (8:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 462 {2,3,7,11} (by decide +kernel)]
  norm_num

lemma weight_465 : c 465 = (8:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 465 {3,5,31} (by decide +kernel)]
  norm_num

lemma weight_474 : c 474 = (4:ℝ)/77 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 474 {2,3,79} (by decide +kernel)]
  norm_num

lemma weight_483 : c 483 = (8:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 483 {3,7,23} (by decide +kernel)]
  norm_num

lemma weights (n : ℕ) (hn : n ∈ selected) : c n = (numerator n : ℝ)/denominator n := by
  simp only [selected, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [numerator, denominator] using weight_1
  · simpa [numerator, denominator] using weight_2
  · simpa [numerator, denominator] using weight_3
  · change c 5 = (2:ℝ)/3
    exact weight_5
  · simpa [numerator, denominator] using weight_6
  · change c 7 = (2:ℝ)/5
    exact weight_7
  · change c 10 = (2:ℝ)/3
    exact weight_10
  · change c 11 = (2:ℝ)/9
    exact weight_11
  · change c 13 = (2:ℝ)/11
    exact weight_13
  · change c 14 = (2:ℝ)/5
    exact weight_14
  · change c 15 = (4:ℝ)/3
    exact weight_15
  · change c 17 = (2:ℝ)/15
    exact weight_17
  · change c 19 = (2:ℝ)/17
    exact weight_19
  · change c 21 = (4:ℝ)/5
    exact weight_21
  · change c 22 = (2:ℝ)/9
    exact weight_22
  · change c 23 = (2:ℝ)/21
    exact weight_23
  · change c 26 = (2:ℝ)/11
    exact weight_26
  · change c 29 = (2:ℝ)/27
    exact weight_29
  · change c 30 = (4:ℝ)/3
    exact weight_30
  · change c 31 = (2:ℝ)/29
    exact weight_31
  · change c 33 = (4:ℝ)/9
    exact weight_33
  · change c 34 = (2:ℝ)/15
    exact weight_34
  · change c 35 = (4:ℝ)/15
    exact weight_35
  · change c 37 = (2:ℝ)/35
    exact weight_37
  · change c 38 = (2:ℝ)/17
    exact weight_38
  · change c 39 = (4:ℝ)/11
    exact weight_39
  · change c 41 = (2:ℝ)/39
    exact weight_41
  · change c 42 = (4:ℝ)/5
    exact weight_42
  · change c 43 = (2:ℝ)/41
    exact weight_43
  · change c 46 = (2:ℝ)/21
    exact weight_46
  · change c 47 = (2:ℝ)/45
    exact weight_47
  · change c 51 = (4:ℝ)/15
    exact weight_51
  · change c 53 = (2:ℝ)/51
    exact weight_53
  · change c 55 = (4:ℝ)/27
    exact weight_55
  · change c 57 = (4:ℝ)/17
    exact weight_57
  · change c 58 = (2:ℝ)/27
    exact weight_58
  · change c 59 = (2:ℝ)/57
    exact weight_59
  · change c 61 = (2:ℝ)/59
    exact weight_61
  · change c 62 = (2:ℝ)/29
    exact weight_62
  · change c 65 = (4:ℝ)/33
    exact weight_65
  · change c 66 = (4:ℝ)/9
    exact weight_66
  · change c 69 = (4:ℝ)/21
    exact weight_69
  · change c 70 = (4:ℝ)/15
    exact weight_70
  · change c 74 = (2:ℝ)/35
    exact weight_74
  · change c 77 = (4:ℝ)/45
    exact weight_77
  · change c 78 = (4:ℝ)/11
    exact weight_78
  · change c 82 = (2:ℝ)/39
    exact weight_82
  · change c 85 = (4:ℝ)/45
    exact weight_85
  · change c 86 = (2:ℝ)/41
    exact weight_86
  · change c 87 = (4:ℝ)/27
    exact weight_87
  · change c 91 = (4:ℝ)/55
    exact weight_91
  · change c 93 = (4:ℝ)/29
    exact weight_93
  · change c 94 = (2:ℝ)/45
    exact weight_94
  · change c 95 = (4:ℝ)/51
    exact weight_95
  · change c 102 = (4:ℝ)/15
    exact weight_102
  · change c 105 = (8:ℝ)/15
    exact weight_105
  · change c 106 = (2:ℝ)/51
    exact weight_106
  · change c 110 = (4:ℝ)/27
    exact weight_110
  · change c 111 = (4:ℝ)/35
    exact weight_111
  · change c 114 = (4:ℝ)/17
    exact weight_114
  · change c 115 = (4:ℝ)/63
    exact weight_115
  · change c 118 = (2:ℝ)/57
    exact weight_118
  · change c 119 = (4:ℝ)/75
    exact weight_119
  · change c 122 = (2:ℝ)/59
    exact weight_122
  · change c 123 = (4:ℝ)/39
    exact weight_123
  · change c 129 = (4:ℝ)/41
    exact weight_129
  · change c 130 = (4:ℝ)/33
    exact weight_130
  · change c 133 = (4:ℝ)/85
    exact weight_133
  · change c 138 = (4:ℝ)/21
    exact weight_138
  · change c 141 = (4:ℝ)/45
    exact weight_141
  · change c 143 = (4:ℝ)/99
    exact weight_143
  · change c 145 = (4:ℝ)/81
    exact weight_145
  · change c 154 = (4:ℝ)/45
    exact weight_154
  · change c 155 = (4:ℝ)/87
    exact weight_155
  · change c 159 = (4:ℝ)/51
    exact weight_159
  · change c 161 = (4:ℝ)/105
    exact weight_161
  · change c 165 = (8:ℝ)/27
    exact weight_165
  · change c 170 = (4:ℝ)/45
    exact weight_170
  · change c 174 = (4:ℝ)/27
    exact weight_174
  · change c 177 = (4:ℝ)/57
    exact weight_177
  · change c 182 = (4:ℝ)/55
    exact weight_182
  · change c 183 = (4:ℝ)/59
    exact weight_183
  · change c 185 = (4:ℝ)/105
    exact weight_185
  · change c 186 = (4:ℝ)/29
    exact weight_186
  · change c 190 = (4:ℝ)/51
    exact weight_190
  · change c 195 = (8:ℝ)/33
    exact weight_195
  · change c 201 = (4:ℝ)/65
    exact weight_201
  · change c 205 = (4:ℝ)/117
    exact weight_205
  · change c 210 = (8:ℝ)/15
    exact weight_210
  · change c 213 = (4:ℝ)/69
    exact weight_213
  · change c 219 = (4:ℝ)/71
    exact weight_219
  · change c 222 = (4:ℝ)/35
    exact weight_222
  · change c 230 = (4:ℝ)/63
    exact weight_230
  · change c 231 = (8:ℝ)/45
    exact weight_231
  · change c 237 = (4:ℝ)/77
    exact weight_237
  · change c 238 = (4:ℝ)/75
    exact weight_238
  · change c 246 = (4:ℝ)/39
    exact weight_246
  · change c 249 = (4:ℝ)/81
    exact weight_249
  · change c 255 = (8:ℝ)/45
    exact weight_255
  · change c 258 = (4:ℝ)/41
    exact weight_258
  · change c 266 = (4:ℝ)/85
    exact weight_266
  · change c 267 = (4:ℝ)/87
    exact weight_267
  · change c 273 = (8:ℝ)/55
    exact weight_273
  · change c 282 = (4:ℝ)/45
    exact weight_282
  · change c 285 = (8:ℝ)/51
    exact weight_285
  · change c 286 = (4:ℝ)/99
    exact weight_286
  · change c 290 = (4:ℝ)/81
    exact weight_290
  · change c 291 = (4:ℝ)/95
    exact weight_291
  · change c 303 = (4:ℝ)/99
    exact weight_303
  · change c 309 = (4:ℝ)/101
    exact weight_309
  · change c 310 = (4:ℝ)/87
    exact weight_310
  · change c 318 = (4:ℝ)/51
    exact weight_318
  · change c 321 = (4:ℝ)/105
    exact weight_321
  · change c 322 = (4:ℝ)/105
    exact weight_322
  · change c 327 = (4:ℝ)/107
    exact weight_327
  · change c 330 = (8:ℝ)/27
    exact weight_330
  · change c 339 = (4:ℝ)/111
    exact weight_339
  · change c 345 = (8:ℝ)/63
    exact weight_345
  · change c 354 = (4:ℝ)/57
    exact weight_354
  · change c 357 = (8:ℝ)/75
    exact weight_357
  · change c 366 = (4:ℝ)/59
    exact weight_366
  · change c 370 = (4:ℝ)/105
    exact weight_370
  · change c 385 = (8:ℝ)/135
    exact weight_385
  · change c 390 = (8:ℝ)/33
    exact weight_390
  · change c 399 = (8:ℝ)/85
    exact weight_399
  · change c 402 = (4:ℝ)/65
    exact weight_402
  · change c 410 = (4:ℝ)/117
    exact weight_410
  · change c 426 = (4:ℝ)/69
    exact weight_426
  · change c 429 = (8:ℝ)/99
    exact weight_429
  · change c 435 = (8:ℝ)/81
    exact weight_435
  · change c 438 = (4:ℝ)/71
    exact weight_438
  · change c 455 = (8:ℝ)/165
    exact weight_455
  · change c 462 = (8:ℝ)/45
    exact weight_462
  · change c 465 = (8:ℝ)/87
    exact weight_465
  · change c 474 = (4:ℝ)/77
    exact weight_474
  · change c 483 = (8:ℝ)/105
    exact weight_483


lemma denominator_pos (n : ℕ) : 0 < denominator n := by
  unfold denominator
  split <;> decide +kernel

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

lemma log_98 : Real.log (4*(98:ℝ)) ≤ (1493/250) := by
  have h := Real.log_div_le_sum_range_add (x := ((17/81):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (392:ℝ) = 8*Real.log 2 + Real.log ((49/32):ℝ) := by
    rw [show (392:ℝ) = 2^8*(49/32) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_80 (z : ℝ) (hl : 80 ≤ z) (hu : z ≤ 98) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 80 98 (1493/250) z
    (by norm_num) hl hu log_98 (by norm_num)
  have hi : roundedSum 80 = 14434778 := by decide +kernel
  have hb := lower 80 (by norm_num)
  rw [hi] at hb
  have hr : ((1493/250):ℝ)^2/(5/2)/(1-((80+1)/(16*80^2))*((1493/250)^2/(5/2))) ≤ (14434778:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_115 : Real.log (4*(115:ℝ)) ≤ (1227/200) := by
  have h := Real.log_div_le_sum_range_add (x := ((51/179):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (460:ℝ) = 8*Real.log 2 + Real.log ((115/64):ℝ) := by
    rw [show (460:ℝ) = 2^8*(115/64) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_98 (z : ℝ) (hl : 98 ≤ z) (hu : z ≤ 115) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 98 115 (1227/200) z
    (by norm_num) hl hu log_115 (by norm_num)
  have hi : roundedSum 98 = 15234915 := by decide +kernel
  have hb := lower 98 (by norm_num)
  rw [hi] at hb
  have hr : ((1227/200):ℝ)^2/(5/2)/(1-((98+1)/(16*98^2))*((1227/200)^2/(5/2))) ≤ (15234915:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_143 : Real.log (4*(143:ℝ)) ≤ (127/20) := by
  have h := Real.log_div_le_sum_range_add (x := ((15/271):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (572:ℝ) = 9*Real.log 2 + Real.log ((143/128):ℝ) := by
    rw [show (572:ℝ) = 2^9*(143/128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_115 (z : ℝ) (hl : 115 ≤ z) (hu : z ≤ 143) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 115 143 (127/20) z
    (by norm_num) hl hu log_143 (by norm_num)
  have hi : roundedSum 115 = 16308968 := by decide +kernel
  have hb := lower 115 (by norm_num)
  rw [hi] at hb
  have hr : ((127/20):ℝ)^2/(5/2)/(1-((115+1)/(16*115^2))*((127/20)^2/(5/2))) ≤ (16308968:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_173 : Real.log (4*(173:ℝ)) ≤ (327/50) := by
  have h := Real.log_div_le_sum_range_add (x := ((45/301):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (692:ℝ) = 9*Real.log 2 + Real.log ((173/128):ℝ) := by
    rw [show (692:ℝ) = 2^9*(173/128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_143 (z : ℝ) (hl : 143 ≤ z) (hu : z ≤ 173) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 143 173 (327/50) z
    (by norm_num) hl hu log_173 (by norm_num)
  have hi : roundedSum 143 = 17239140 := by decide +kernel
  have hb := lower 143 (by norm_num)
  rw [hi] at hb
  have hr : ((327/50):ℝ)^2/(5/2)/(1-((143+1)/(16*143^2))*((327/50)^2/(5/2))) ≤ (17239140:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_201 : Real.log (4*(201:ℝ)) ≤ (6691/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((73/329):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (804:ℝ) = 9*Real.log 2 + Real.log ((201/128):ℝ) := by
    rw [show (804:ℝ) = 2^9*(201/128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_173 (z : ℝ) (hl : 173 ≤ z) (hu : z ≤ 201) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 173 201 (6691/1000) z
    (by norm_num) hl hu log_201 (by norm_num)
  have hi : roundedSum 173 = 18032380 := by decide +kernel
  have hb := lower 173 (by norm_num)
  rw [hi] at hb
  have hr : ((6691/1000):ℝ)^2/(5/2)/(1-((173+1)/(16*173^2))*((6691/1000)^2/(5/2))) ≤ (18032380:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_233 : Real.log (4*(233:ℝ)) ≤ (6841/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((105/361):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (932:ℝ) = 9*Real.log 2 + Real.log ((233/128):ℝ) := by
    rw [show (932:ℝ) = 2^9*(233/128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_201 (z : ℝ) (hl : 201 ≤ z) (hu : z ≤ 233) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 201 233 (6841/1000) z
    (by norm_num) hl hu log_233 (by norm_num)
  have hi : roundedSum 201 = 18849749 := by decide +kernel
  have hb := lower 201 (by norm_num)
  rw [hi] at hb
  have hr : ((6841/1000):ℝ)^2/(5/2)/(1-((201+1)/(16*201^2))*((6841/1000)^2/(5/2))) ≤ (18849749:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_275 : Real.log (4*(275:ℝ)) ≤ (1751/250) := by
  have h := Real.log_div_le_sum_range_add (x := ((19/531):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1100:ℝ) = 10*Real.log 2 + Real.log ((275/256):ℝ) := by
    rw [show (1100:ℝ) = 2^10*(275/256) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_233 (z : ℝ) (hl : 233 ≤ z) (hu : z ≤ 275) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 233 275 (1751/250) z
    (by norm_num) hl hu log_275 (by norm_num)
  have hi : roundedSum 233 = 19731996 := by decide +kernel
  have hb := lower 233 (by norm_num)
  rw [hi] at hb
  have hr : ((1751/250):ℝ)^2/(5/2)/(1-((233+1)/(16*233^2))*((1751/250)^2/(5/2))) ≤ (19731996:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_317 : Real.log (4*(317:ℝ)) ≤ (3573/500) := by
  have h := Real.log_div_le_sum_range_add (x := ((61/573):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1268:ℝ) = 10*Real.log 2 + Real.log ((317/256):ℝ) := by
    rw [show (1268:ℝ) = 2^10*(317/256) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_275 (z : ℝ) (hl : 275 ≤ z) (hu : z ≤ 317) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 275 317 (3573/500) z
    (by norm_num) hl hu log_317 (by norm_num)
  have hi : roundedSum 275 = 20530154 := by decide +kernel
  have hb := lower 275 (by norm_num)
  rw [hi] at hb
  have hr : ((3573/500):ℝ)^2/(5/2)/(1-((275+1)/(16*275^2))*((3573/500)^2/(5/2))) ≤ (20530154:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_353 : Real.log (4*(353:ℝ)) ≤ (7253/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((97/609):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1412:ℝ) = 10*Real.log 2 + Real.log ((353/256):ℝ) := by
    rw [show (1412:ℝ) = 2^10*(353/256) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_317 (z : ℝ) (hl : 317 ≤ z) (hu : z ≤ 353) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 317 353 (7253/1000) z
    (by norm_num) hl hu log_353 (by norm_num)
  have hi : roundedSum 317 = 21136014 := by decide +kernel
  have hb := lower 317 (by norm_num)
  rw [hi] at hb
  have hr : ((7253/1000):ℝ)^2/(5/2)/(1-((317+1)/(16*317^2))*((7253/1000)^2/(5/2))) ≤ (21136014:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_391 : Real.log (4*(391:ℝ)) ≤ (1839/250) := by
  have h := Real.log_div_le_sum_range_add (x := ((135/647):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1564:ℝ) = 10*Real.log 2 + Real.log ((391/256):ℝ) := by
    rw [show (1564:ℝ) = 2^10*(391/256) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_353 (z : ℝ) (hl : 353 ≤ z) (hu : z ≤ 391) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 353 391 (1839/250) z
    (by norm_num) hl hu log_391 (by norm_num)
  have hi : roundedSum 353 = 21729462 := by decide +kernel
  have hb := lower 353 (by norm_num)
  rw [hi] at hb
  have hr : ((1839/250):ℝ)^2/(5/2)/(1-((353+1)/(16*353^2))*((1839/250)^2/(5/2))) ≤ (21729462:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_428 : Real.log (4*(428:ℝ)) ≤ (931/125) := by
  have h := Real.log_div_le_sum_range_add (x := ((43/171):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1712:ℝ) = 10*Real.log 2 + Real.log ((107/64):ℝ) := by
    rw [show (1712:ℝ) = 2^10*(107/64) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_391 (z : ℝ) (hl : 391 ≤ z) (hu : z ≤ 428) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 391 428 (931/125) z
    (by norm_num) hl hu log_428 (by norm_num)
  have hi : roundedSum 391 = 22275922 := by decide +kernel
  have hb := lower 391 (by norm_num)
  rw [hi] at hb
  have hr : ((931/125):ℝ)^2/(5/2)/(1-((391+1)/(16*391^2))*((931/125)^2/(5/2))) ≤ (22275922:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_454 : Real.log (4*(454:ℝ)) ≤ (1877/250) := by
  have h := Real.log_div_le_sum_range_add (x := ((99/355):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1816:ℝ) = 10*Real.log 2 + Real.log ((227/128):ℝ) := by
    rw [show (1816:ℝ) = 2^10*(227/128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_428 (z : ℝ) (hl : 428 ≤ z) (hu : z ≤ 454) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 428 454 (1877/250) z
    (by norm_num) hl hu log_454 (by norm_num)
  have hi : roundedSum 428 = 22624844 := by decide +kernel
  have hb := lower 428 (by norm_num)
  rw [hi] at hb
  have hr : ((1877/250):ℝ)^2/(5/2)/(1-((428+1)/(16*428^2))*((1877/250)^2/(5/2))) ≤ (22624844:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_474 : Real.log (4*(474:ℝ)) ≤ (944/125) := by
  have h := Real.log_div_le_sum_range_add (x := ((109/365):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1896:ℝ) = 10*Real.log 2 + Real.log ((237/128):ℝ) := by
    rw [show (1896:ℝ) = 2^10*(237/128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_454 (z : ℝ) (hl : 454 ≤ z) (hu : z ≤ 474) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 454 474 (944/125) z
    (by norm_num) hl hu log_474 (by norm_num)
  have hi : roundedSum 454 = 22888549 := by decide +kernel
  have hb := lower 454 (by norm_num)
  rw [hi] at hb
  have hr : ((944/125):ℝ)^2/(5/2)/(1-((454+1)/(16*454^2))*((944/125)^2/(5/2))) ≤ (22888549:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_496 : Real.log (4*(496:ℝ)) ≤ (7599/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((15/47):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (1984:ℝ) = 10*Real.log 2 + Real.log ((31/16):ℝ) := by
    rw [show (1984:ℝ) = 2^10*(31/16) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_474 (z : ℝ) (hl : 474 ≤ z) (hu : z ≤ 496) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 474 496 (7599/1000) z
    (by norm_num) hl hu log_496 (by norm_num)
  have hi : roundedSum 474 = 23180109 := by decide +kernel
  have hb := lower 474 (by norm_num)
  rw [hi] at hb
  have hr : ((7599/1000):ℝ)^2/(5/2)/(1-((474+1)/(16*474^2))*((7599/1000)^2/(5/2))) ≤ (23180109:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_500 : Real.log (4*(500:ℝ)) ≤ (951/125) := by
  have h := Real.log_div_le_sum_range_add (x := ((61/189):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (2000:ℝ) = 10*Real.log 2 + Real.log ((125/64):ℝ) := by
    rw [show (2000:ℝ) = 2^10*(125/64) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_496 (z : ℝ) (hl : 496 ≤ z) (hu : z ≤ 500) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 496 500 (951/125) z
    (by norm_num) hl hu log_500 (by norm_num)
  have hi : roundedSum 496 = 23330331 := by decide +kernel
  have hb := lower 496 (by norm_num)
  rw [hi] at hb
  have hr : ((951/125):ℝ)^2/(5/2)/(1-((496+1)/(16*496^2))*((951/125)^2/(5/2))) ≤ (23330331:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

end

end ReciprocalPilot

theorem solution (z : ℝ) (hz : 40 ≤ z) (hupper : z ≤ 500) :
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

  by_cases h98 : z ≤ 98
  · exact ReciprocalPilot.cell_80 z (by linarith) h98

  by_cases h115 : z ≤ 115
  · exact ReciprocalPilot.cell_98 z (by linarith) h115

  by_cases h143 : z ≤ 143
  · exact ReciprocalPilot.cell_115 z (by linarith) h143

  by_cases h173 : z ≤ 173
  · exact ReciprocalPilot.cell_143 z (by linarith) h173

  by_cases h201 : z ≤ 201
  · exact ReciprocalPilot.cell_173 z (by linarith) h201

  by_cases h233 : z ≤ 233
  · exact ReciprocalPilot.cell_201 z (by linarith) h233

  by_cases h275 : z ≤ 275
  · exact ReciprocalPilot.cell_233 z (by linarith) h275

  by_cases h317 : z ≤ 317
  · exact ReciprocalPilot.cell_275 z (by linarith) h317

  by_cases h353 : z ≤ 353
  · exact ReciprocalPilot.cell_317 z (by linarith) h353

  by_cases h391 : z ≤ 391
  · exact ReciprocalPilot.cell_353 z (by linarith) h391

  by_cases h428 : z ≤ 428
  · exact ReciprocalPilot.cell_391 z (by linarith) h428

  by_cases h454 : z ≤ 454
  · exact ReciprocalPilot.cell_428 z (by linarith) h454

  by_cases h474 : z ≤ 474
  · exact ReciprocalPilot.cell_454 z (by linarith) h474

  by_cases h496 : z ≤ 496
  · exact ReciprocalPilot.cell_474 z (by linarith) h496

  exact ReciprocalPilot.cell_496 z (by linarith) hupper

#print axioms solution
