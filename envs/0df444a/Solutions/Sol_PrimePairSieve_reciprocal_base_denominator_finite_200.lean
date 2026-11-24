-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_finite_200
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:22:01.70053+00:00
-- url     : https://prove2.me/submissions/359b6988-cf02-4bf5-be34-332a547efee2

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

def selected : Finset ℕ := {1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,26,29,30,31,33,34,35,37,38,39,41,42,43,46,47,51,53,55,57,58,59,61,62,65,66,67,69,70,71,73,74,77,78,79,82,83,85,86,87,89,91,93,94,95,97,101,102,103,105,106,107,109,110,111,113,114,115,118,119,122,123,127,129,130,131,133,134,137,138,139,141,142,143,145,146,149,151,154,155,157,158,159,161,163,165,166,167,170,173,174,177,178,179,181,182,183,185,186}

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
  | 101 => 2
  | 102 => 4
  | 103 => 2
  | 105 => 8
  | 106 => 2
  | 107 => 2
  | 109 => 2
  | 110 => 4
  | 111 => 4
  | 113 => 2
  | 114 => 4
  | 115 => 4
  | 118 => 2
  | 119 => 4
  | 122 => 2
  | 123 => 4
  | 127 => 2
  | 129 => 4
  | 130 => 4
  | 131 => 2
  | 133 => 4
  | 134 => 2
  | 137 => 2
  | 138 => 4
  | 139 => 2
  | 141 => 4
  | 142 => 2
  | 143 => 4
  | 145 => 4
  | 146 => 2
  | 149 => 2
  | 151 => 2
  | 154 => 4
  | 155 => 4
  | 157 => 2
  | 158 => 2
  | 159 => 4
  | 161 => 4
  | 163 => 2
  | 165 => 8
  | 166 => 2
  | 167 => 2
  | 170 => 4
  | 173 => 2
  | 174 => 4
  | 177 => 4
  | 178 => 2
  | 179 => 2
  | 181 => 2
  | 182 => 4
  | 183 => 4
  | 185 => 4
  | 186 => 4
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
  | 101 => 99
  | 102 => 15
  | 103 => 101
  | 105 => 15
  | 106 => 51
  | 107 => 105
  | 109 => 107
  | 110 => 27
  | 111 => 35
  | 113 => 111
  | 114 => 17
  | 115 => 63
  | 118 => 57
  | 119 => 75
  | 122 => 59
  | 123 => 39
  | 127 => 125
  | 129 => 41
  | 130 => 33
  | 131 => 129
  | 133 => 85
  | 134 => 65
  | 137 => 135
  | 138 => 21
  | 139 => 137
  | 141 => 45
  | 142 => 69
  | 143 => 99
  | 145 => 81
  | 146 => 71
  | 149 => 147
  | 151 => 149
  | 154 => 45
  | 155 => 87
  | 157 => 155
  | 158 => 77
  | 159 => 51
  | 161 => 105
  | 163 => 161
  | 165 => 27
  | 166 => 81
  | 167 => 165
  | 170 => 45
  | 173 => 171
  | 174 => 27
  | 177 => 57
  | 178 => 87
  | 179 => 177
  | 181 => 179
  | 182 => 55
  | 183 => 59
  | 185 => 105
  | 186 => 29
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

lemma weight_101 : c 101 = (2:ℝ)/99 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 101 {101} (by decide +kernel)]
  norm_num

lemma weight_102 : c 102 = (4:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 102 {2,3,17} (by decide +kernel)]
  norm_num

lemma weight_103 : c 103 = (2:ℝ)/101 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 103 {103} (by decide +kernel)]
  norm_num

lemma weight_105 : c 105 = (8:ℝ)/15 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 105 {3,5,7} (by decide +kernel)]
  norm_num

lemma weight_106 : c 106 = (2:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 106 {2,53} (by decide +kernel)]
  norm_num

lemma weight_107 : c 107 = (2:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 107 {107} (by decide +kernel)]
  norm_num

lemma weight_109 : c 109 = (2:ℝ)/107 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 109 {109} (by decide +kernel)]
  norm_num

lemma weight_110 : c 110 = (4:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 110 {2,5,11} (by decide +kernel)]
  norm_num

lemma weight_111 : c 111 = (4:ℝ)/35 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 111 {3,37} (by decide +kernel)]
  norm_num

lemma weight_113 : c 113 = (2:ℝ)/111 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 113 {113} (by decide +kernel)]
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

lemma weight_127 : c 127 = (2:ℝ)/125 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 127 {127} (by decide +kernel)]
  norm_num

lemma weight_129 : c 129 = (4:ℝ)/41 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 129 {3,43} (by decide +kernel)]
  norm_num

lemma weight_130 : c 130 = (4:ℝ)/33 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 130 {2,5,13} (by decide +kernel)]
  norm_num

lemma weight_131 : c 131 = (2:ℝ)/129 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 131 {131} (by decide +kernel)]
  norm_num

lemma weight_133 : c 133 = (4:ℝ)/85 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 133 {7,19} (by decide +kernel)]
  norm_num

lemma weight_134 : c 134 = (2:ℝ)/65 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 134 {2,67} (by decide +kernel)]
  norm_num

lemma weight_137 : c 137 = (2:ℝ)/135 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 137 {137} (by decide +kernel)]
  norm_num

lemma weight_138 : c 138 = (4:ℝ)/21 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 138 {2,3,23} (by decide +kernel)]
  norm_num

lemma weight_139 : c 139 = (2:ℝ)/137 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 139 {139} (by decide +kernel)]
  norm_num

lemma weight_141 : c 141 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 141 {3,47} (by decide +kernel)]
  norm_num

lemma weight_142 : c 142 = (2:ℝ)/69 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 142 {2,71} (by decide +kernel)]
  norm_num

lemma weight_143 : c 143 = (4:ℝ)/99 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 143 {11,13} (by decide +kernel)]
  norm_num

lemma weight_145 : c 145 = (4:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 145 {5,29} (by decide +kernel)]
  norm_num

lemma weight_146 : c 146 = (2:ℝ)/71 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 146 {2,73} (by decide +kernel)]
  norm_num

lemma weight_149 : c 149 = (2:ℝ)/147 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 149 {149} (by decide +kernel)]
  norm_num

lemma weight_151 : c 151 = (2:ℝ)/149 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 151 {151} (by decide +kernel)]
  norm_num

lemma weight_154 : c 154 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 154 {2,7,11} (by decide +kernel)]
  norm_num

lemma weight_155 : c 155 = (4:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 155 {5,31} (by decide +kernel)]
  norm_num

lemma weight_157 : c 157 = (2:ℝ)/155 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 157 {157} (by decide +kernel)]
  norm_num

lemma weight_158 : c 158 = (2:ℝ)/77 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 158 {2,79} (by decide +kernel)]
  norm_num

lemma weight_159 : c 159 = (4:ℝ)/51 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 159 {3,53} (by decide +kernel)]
  norm_num

lemma weight_161 : c 161 = (4:ℝ)/105 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 161 {7,23} (by decide +kernel)]
  norm_num

lemma weight_163 : c 163 = (2:ℝ)/161 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 163 {163} (by decide +kernel)]
  norm_num

lemma weight_165 : c 165 = (8:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 165 {3,5,11} (by decide +kernel)]
  norm_num

lemma weight_166 : c 166 = (2:ℝ)/81 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 166 {2,83} (by decide +kernel)]
  norm_num

lemma weight_167 : c 167 = (2:ℝ)/165 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 167 {167} (by decide +kernel)]
  norm_num

lemma weight_170 : c 170 = (4:ℝ)/45 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 170 {2,5,17} (by decide +kernel)]
  norm_num

lemma weight_173 : c 173 = (2:ℝ)/171 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 173 {173} (by decide +kernel)]
  norm_num

lemma weight_174 : c 174 = (4:ℝ)/27 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 174 {2,3,29} (by decide +kernel)]
  norm_num

lemma weight_177 : c 177 = (4:ℝ)/57 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 177 {3,59} (by decide +kernel)]
  norm_num

lemma weight_178 : c 178 = (2:ℝ)/87 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 178 {2,89} (by decide +kernel)]
  norm_num

lemma weight_179 : c 179 = (2:ℝ)/177 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 179 {179} (by decide +kernel)]
  norm_num

lemma weight_181 : c 181 = (2:ℝ)/179 := by
  unfold c
  rw [ReciprocalWeightCertificate.weight_eq 181 {181} (by decide +kernel)]
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

lemma weights (n : ℕ) (hn : n ∈ selected) : c n = (numerator n : ℝ)/denominator n := by
  simp only [selected, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · change c 67 = (2:ℝ)/65
    exact weight_67
  · change c 69 = (4:ℝ)/21
    exact weight_69
  · change c 70 = (4:ℝ)/15
    exact weight_70
  · change c 71 = (2:ℝ)/69
    exact weight_71
  · change c 73 = (2:ℝ)/71
    exact weight_73
  · change c 74 = (2:ℝ)/35
    exact weight_74
  · change c 77 = (4:ℝ)/45
    exact weight_77
  · change c 78 = (4:ℝ)/11
    exact weight_78
  · change c 79 = (2:ℝ)/77
    exact weight_79
  · change c 82 = (2:ℝ)/39
    exact weight_82
  · change c 83 = (2:ℝ)/81
    exact weight_83
  · change c 85 = (4:ℝ)/45
    exact weight_85
  · change c 86 = (2:ℝ)/41
    exact weight_86
  · change c 87 = (4:ℝ)/27
    exact weight_87
  · change c 89 = (2:ℝ)/87
    exact weight_89
  · change c 91 = (4:ℝ)/55
    exact weight_91
  · change c 93 = (4:ℝ)/29
    exact weight_93
  · change c 94 = (2:ℝ)/45
    exact weight_94
  · change c 95 = (4:ℝ)/51
    exact weight_95
  · change c 97 = (2:ℝ)/95
    exact weight_97
  · change c 101 = (2:ℝ)/99
    exact weight_101
  · change c 102 = (4:ℝ)/15
    exact weight_102
  · change c 103 = (2:ℝ)/101
    exact weight_103
  · change c 105 = (8:ℝ)/15
    exact weight_105
  · change c 106 = (2:ℝ)/51
    exact weight_106
  · change c 107 = (2:ℝ)/105
    exact weight_107
  · change c 109 = (2:ℝ)/107
    exact weight_109
  · change c 110 = (4:ℝ)/27
    exact weight_110
  · change c 111 = (4:ℝ)/35
    exact weight_111
  · change c 113 = (2:ℝ)/111
    exact weight_113
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
  · change c 127 = (2:ℝ)/125
    exact weight_127
  · change c 129 = (4:ℝ)/41
    exact weight_129
  · change c 130 = (4:ℝ)/33
    exact weight_130
  · change c 131 = (2:ℝ)/129
    exact weight_131
  · change c 133 = (4:ℝ)/85
    exact weight_133
  · change c 134 = (2:ℝ)/65
    exact weight_134
  · change c 137 = (2:ℝ)/135
    exact weight_137
  · change c 138 = (4:ℝ)/21
    exact weight_138
  · change c 139 = (2:ℝ)/137
    exact weight_139
  · change c 141 = (4:ℝ)/45
    exact weight_141
  · change c 142 = (2:ℝ)/69
    exact weight_142
  · change c 143 = (4:ℝ)/99
    exact weight_143
  · change c 145 = (4:ℝ)/81
    exact weight_145
  · change c 146 = (2:ℝ)/71
    exact weight_146
  · change c 149 = (2:ℝ)/147
    exact weight_149
  · change c 151 = (2:ℝ)/149
    exact weight_151
  · change c 154 = (4:ℝ)/45
    exact weight_154
  · change c 155 = (4:ℝ)/87
    exact weight_155
  · change c 157 = (2:ℝ)/155
    exact weight_157
  · change c 158 = (2:ℝ)/77
    exact weight_158
  · change c 159 = (4:ℝ)/51
    exact weight_159
  · change c 161 = (4:ℝ)/105
    exact weight_161
  · change c 163 = (2:ℝ)/161
    exact weight_163
  · change c 165 = (8:ℝ)/27
    exact weight_165
  · change c 166 = (2:ℝ)/81
    exact weight_166
  · change c 167 = (2:ℝ)/165
    exact weight_167
  · change c 170 = (4:ℝ)/45
    exact weight_170
  · change c 173 = (2:ℝ)/171
    exact weight_173
  · change c 174 = (4:ℝ)/27
    exact weight_174
  · change c 177 = (4:ℝ)/57
    exact weight_177
  · change c 178 = (2:ℝ)/87
    exact weight_178
  · change c 179 = (2:ℝ)/177
    exact weight_179
  · change c 181 = (2:ℝ)/179
    exact weight_181
  · change c 182 = (4:ℝ)/55
    exact weight_182
  · change c 183 = (4:ℝ)/59
    exact weight_183
  · change c 185 = (4:ℝ)/105
    exact weight_185
  · change c 186 = (4:ℝ)/29
    exact weight_186


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

lemma log_118 : Real.log (4*(118:ℝ)) ≤ (3081/500) := by
  have h := Real.log_div_le_sum_range_add (x := ((27/91):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (472:ℝ) = 8*Real.log 2 + Real.log ((59/32):ℝ) := by
    rw [show (472:ℝ) = 2^8*(59/32) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_99 (z : ℝ) (hl : 99 ≤ z) (hu : z ≤ 118) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 99 118 (3081/500) z
    (by norm_num) hl hu log_118 (by norm_num)
  have hi : roundedSum 99 = 15359992 := by decide +kernel
  have hb := lower 99 (by norm_num)
  rw [hi] at hb
  have hr : ((3081/500):ℝ)^2/(5/2)/(1-((99+1)/(16*99^2))*((3081/500)^2/(5/2))) ≤ (15359992:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_150 : Real.log (4*(150:ℝ)) ≤ (6397/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((11/139):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (600:ℝ) = 9*Real.log 2 + Real.log ((75/64):ℝ) := by
    rw [show (600:ℝ) = 2^9*(75/64) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_118 (z : ℝ) (hl : 118 ≤ z) (hu : z ≤ 150) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 118 150 (6397/1000) z
    (by norm_num) hl hu log_150 (by norm_num)
  have hi : roundedSum 118 = 16549422 := by decide +kernel
  have hb := lower 118 (by norm_num)
  rw [hi] at hb
  have hr : ((6397/1000):ℝ)^2/(5/2)/(1-((118+1)/(16*118^2))*((6397/1000)^2/(5/2))) ≤ (16549422:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_186 : Real.log (4*(186:ℝ)) ≤ (6613/1000) := by
  have h := Real.log_div_le_sum_range_add (x := ((29/157):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (744:ℝ) = 9*Real.log 2 + Real.log ((93/64):ℝ) := by
    rw [show (744:ℝ) = 2^9*(93/64) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_150 (z : ℝ) (hl : 150 ≤ z) (hu : z ≤ 186) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 150 186 (6613/1000) z
    (by norm_num) hl hu log_186 (by norm_num)
  have hi : roundedSum 150 = 17638588 := by decide +kernel
  have hb := lower 150 (by norm_num)
  rw [hi] at hb
  have hr : ((6613/1000):ℝ)^2/(5/2)/(1-((150+1)/(16*150^2))*((6613/1000)^2/(5/2))) ≤ (17638588:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

lemma log_200 : Real.log (4*(200:ℝ)) ≤ (3343/500) := by
  have h := Real.log_div_le_sum_range_add (x := ((9/41):ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (800:ℝ) = 9*Real.log 2 + Real.log ((25/16):ℝ) := by
    rw [show (800:ℝ) = 2^9*(25/16) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma cell_186 (z : ℝ) (hl : 186 ≤ z) (hu : z ≤ 200) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n/(1+(n:ℝ)/z) := by
  apply PrimePairSieve.reciprocal_base_denominator_interval_certificate 186 200 (3343/500) z
    (by norm_num) hl hu log_200 (by norm_num)
  have hi : roundedSum 186 = 18838309 := by decide +kernel
  have hb := lower 186 (by norm_num)
  rw [hi] at hb
  have hr : ((3343/500):ℝ)^2/(5/2)/(1-((186+1)/(16*186^2))*((3343/500)^2/(5/2))) ≤ (18838309:ℝ)/1000000 := by norm_num
  simpa [c] using hr.trans hb

end

end ReciprocalPilot

theorem solution (z : ℝ) (hz : 40 ≤ z) (hupper : z ≤ 200) :
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

  by_cases h118 : z ≤ 118
  · exact ReciprocalPilot.cell_99 z (by linarith) h118

  by_cases h150 : z ≤ 150
  · exact ReciprocalPilot.cell_118 z (by linarith) h150

  by_cases h186 : z ≤ 186
  · exact ReciprocalPilot.cell_150 z (by linarith) h186

  exact ReciprocalPilot.cell_186 z (by linarith) hupper

#print axioms solution
