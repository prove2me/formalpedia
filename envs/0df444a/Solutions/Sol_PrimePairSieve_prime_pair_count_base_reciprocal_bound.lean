-- Prove2me | solution 1 for PrimePairSieve_prime_pair_count_base_reciprocal_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:53:20.407616+00:00
-- url     : https://prove2.me/submissions/ed34ad35-bd22-4e5d-bf6f-b8b128b6e6c1

import Theorems.Thm_PrimePairSieve_reciprocal_weighted_sifted_bound
import Theorems.Thm_PrimePairSieve_divisor_kernel_comparison
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
open scoped BigOperators
namespace PrimePairCount

theorem natural_moduli_sifted
    (hSieve : ∀ (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)),
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹)
    (Q : Finset ℕ) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, 0 < q ∧ Squarefree q ∧ (q : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ q.primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ q.primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*(q : ℝ)*z))⁻¹ := by
  classical
  let e : Q ↪ ℕ+ := ⟨fun q => ⟨q.val, (hQ q.val q.property).1⟩,
    fun a b h => Subtype.ext (congrArg (fun q : ℕ+ => (q : ℕ)) h)⟩
  let R : Finset ℕ+ := Finset.univ.map e
  have hR1 : 1 ∈ R := by
    exact Finset.mem_map.mpr ⟨⟨1,h1⟩, Finset.mem_univ _, rfl⟩
  have hR (q : ℕ+) (hq : q ∈ R) : Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hq
    exact (hQ a.val a.property).2
  have h := hSieve R hR1 N d z hz hR hd A hAN (by
    intro q hq n hn p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hq
    exact hA a.val a.property n hn p hp)
  simp only [R, Finset.sum_map] at h
  change (A.card : ℝ) ≤ (∑ q : Q,
    (∏ p ∈ q.val.primeFactors, if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
    ((N : ℝ)+16*(q.val : ℝ)*z))⁻¹ at h
  rw [Finset.sum_coe_sort Q (fun q : ℕ =>
    (∏ p ∈ q.primeFactors, if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
    ((N : ℝ)+16*(q : ℝ)*z))] at h
  exact h

end PrimePairCount
namespace PrimePairCount

theorem prime_pair_count_reciprocal
    (hSieve : ∀ (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)),
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹)
    (x d : ℕ) (hd0 : 0 < d) (hd : 2 ∣ d) (z : ℝ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤
    (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then
        ∏ p ∈ q.primeFactors,
          if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)
        else 0) / ((x : ℝ)+16*(q : ℝ)*z))⁻¹ + z + 1 := by
  classical
  let Q := (Finset.Icc 1 ⌊z⌋₊).filter Squarefree
  let C := (Finset.range (x+1)).filter
    (fun n => Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x)
  let A := C.filter (fun n : ℕ => z < (n : ℝ))
  have hQ1 : 1 ∈ Q := by
    simp only [Q, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, (Nat.le_floor (by simpa using hz))⟩, squarefree_one⟩
  have hQ (q : ℕ) (hq : q ∈ Q) : 0 < q ∧ Squarefree q ∧ (q : ℝ) ≤ z := by
    obtain ⟨hq, hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
    exact ⟨hlo, hs, (Nat.le_floor_iff (by linarith)).mp hhi⟩
  have hAN : A ⊆ Finset.range x := by
    intro n hn
    obtain ⟨hnC, _⟩ := Finset.mem_filter.mp hn
    have hnx := (Finset.mem_filter.mp hnC).2.2.2
    exact Finset.mem_range.mpr (by omega)
  have hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ q.primeFactors, ¬ p ∣ n*(n+d) := by
    intro q hq n hn p hp hdiv
    obtain ⟨hnC, hzn⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, hnprime, hndprime, hnx⟩ := Finset.mem_filter.mp hnC
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpq : p ≤ q := Nat.le_of_dvd (hQ q hq).1 (Nat.dvd_of_mem_primeFactors hp)
    have hpz : (p : ℝ) ≤ z := (by exact_mod_cast hpq : (p : ℝ) ≤ q).trans (hQ q hq).2.2
    rcases hprime.dvd_mul.mp hdiv with hpn | hpn
    · have he := (Nat.prime_dvd_prime_iff_eq hprime hnprime).mp hpn
      subst p
      linarith
    · have he := (Nat.prime_dvd_prime_iff_eq hprime hndprime).mp hpn
      subst p
      push_cast at hpz
      have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
  have hsieve := natural_moduli_sifted hSieve Q hQ1 x d z hz hQ hd A hAN hA
  have hden : (∑ q ∈ Q, (∏ p ∈ q.primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
        ((x : ℝ)+16*(q : ℝ)*z)) =
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊, (if Squarefree q then
        ∏ p ∈ q.primeFactors,
          if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)
        else 0) / ((x : ℝ)+16*(q : ℝ)*z) := by
    simp only [Q, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    split_ifs <;> simp
  rw [hden] at hsieve
  have hsub : C ⊆ A ∪ Finset.range (⌊z⌋₊+1) := by
    intro n hn
    by_cases hzn : z < (n : ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn,hzn⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_range.mpr
      have hnz : n ≤ ⌊z⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (le_of_not_gt hzn)
      omega
  have hcard : C.card ≤ A.card + (⌊z⌋₊+1) := by
    simpa only [Finset.card_range] using
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : (C.card : ℝ) ≤ (A.card : ℝ) + (⌊z⌋₊ : ℝ)+1 := by exact_mod_cast hcard
  have hfloor : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hcount : (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) = (C.card : ℝ) := by
    simp only [C, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hcount]
  linarith

end PrimePairCount
set_option autoImplicit false
open scoped BigOperators
namespace PrimePairCount

lemma primorial_cutoff_sum (z : ℝ) (hz : 0 ≤ z) (f : ℕ → ℝ) :
    (∑ q ∈ (primorial ⌊z⌋₊).divisors, if (q : ℝ) ≤ z then f q else 0) =
    ∑ q ∈ Finset.Icc 1 ⌊z⌋₊, if Squarefree q then f q else 0 := by
  have he : ((primorial ⌊z⌋₊).divisors.filter (fun q : ℕ => (q : ℝ) ≤ z)) =
      (Finset.Icc 1 ⌊z⌋₊).filter Squarefree := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hq, hqz⟩
      have hdiv := Nat.dvd_of_mem_divisors hq
      exact ⟨⟨Nat.pos_of_mem_divisors hq, (Nat.le_floor_iff hz).mpr hqz⟩,
        (squarefree_primorial _).squarefree_of_dvd hdiv⟩
    · rintro ⟨⟨hlo,hhi⟩,hsq⟩
      exact ⟨Nat.mem_divisors.mpr ⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hhi),
        primorial_ne_zero _⟩, (Nat.le_floor_iff hz).mp hhi⟩
  rw [← Finset.sum_filter, he, Finset.sum_filter]

lemma weighted_cutoff_antitone (z : ℝ) (hz : 0 < z) :
    Antitone (fun n : ℕ => if (n : ℝ) ≤ z then 1 / (1+(n : ℝ)/z) else 0) := by
  intro m n hmn
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hden (q : ℕ) : 0 < 1+(q : ℝ)/z := by positivity
  by_cases hn : (n : ℝ) ≤ z
  · have hm := hmnR.trans hn
    simp only [if_pos hn,if_pos hm]
    exact one_div_le_one_div_of_le (hden m)
      (add_le_add_right (div_le_div_of_nonneg_right hmnR hz.le) 1)
  · simp only [if_neg hn]
    split_ifs
    · exact (div_pos (by norm_num) (hden m)).le
    · exact le_rfl

lemma correction_prod_le (P d : ℕ) (hd : 0 < d) :
    (∏ p ∈ P.primeFactors, if 2 < p ∧ p ∣ d then ((p : ℝ)-1)/((p : ℝ)-2) else 1) ≤
      ∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1 := by
  let S := P.primeFactors.filter (fun p => 2 < p ∧ p ∣ d)
  let T := d.primeFactors.filter (fun p => 2 < p)
  have hsub : S ⊆ T := by
    intro p hp
    obtain ⟨hp, h2, hpd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,hpd,hd.ne'⟩,h2⟩
  have hone (p : ℕ) (hp : p ∈ T) : 1 ≤ ((p : ℝ)-1)/((p : ℝ)-2) := by
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p-2)).mpr
    linarith
  have h := Finset.prod_le_prod_of_subset_of_one_le hsub
    (fun p hp => le_trans (by norm_num : (0 : ℝ) ≤ 1) (hone p (hsub hp)))
    (fun p hp _ => hone p hp)
  simpa only [S,T,Finset.prod_filter] using h

end PrimePairCount
namespace PrimePairCount

theorem pair_weight_nonneg (q : ℕ) (d : ℕ) (hd : 2 ∣ d) :
    0 ≤ ∏ p ∈ q.primeFactors,
      if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2) := by
  apply Finset.prod_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : 2 ≤ p := hprime.two_le
  split_ifs with hpd
  · have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by norm_num) (by linarith)
  · have hne : p ≠ 2 := by intro h; subst p; exact hpd hd
    have hp3 : (2 : ℝ) < p := by exact_mod_cast (by omega : 2 < p)
    exact div_nonneg (by norm_num) (by linarith)



theorem base_denominator_le
    (hComp : ∀ (P d : ℕ) (hP : Squarefree P) (hd : 2 ∣ d)
    (F : ℕ → ℝ) (hF : Antitone F),
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) * F n) ≤
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p ∣ d then (1 : ℝ) / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) * F n) *
      ∏ p ∈ P.primeFactors,
        if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1)
    (d : ℕ) (hd0 : 0 < d) (hd : 2 ∣ d) (z : ℝ) (hz : 1 ≤ z) :
    (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then ∏ p ∈ q.primeFactors,
        if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)) ≤
    (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then ∏ p ∈ q.primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)) *
      ∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1 := by
  classical
  have hzpos : 0 < z := by linarith
  have h := hComp (primorial ⌊z⌋₊) d (squarefree_primorial _) hd
    (fun q => if (q : ℝ) ≤ z then 1/(1+(q : ℝ)/z) else 0)
    (weighted_cutoff_antitone z hzpos)
  simp only [mul_ite,mul_zero,mul_one_div] at h
  rw [primorial_cutoff_sum z hzpos.le, primorial_cutoff_sum z hzpos.le] at h
  have hnonneg : 0 ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      if Squarefree q then (∏ p ∈ q.primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) / (1+(q : ℝ)/z) else 0 := by
    apply Finset.sum_nonneg
    intro q hq
    split_ifs
    · exact div_nonneg (pair_weight_nonneg q d hd) (by positivity)
    · exact le_rfl
  have hmul := mul_le_mul_of_nonneg_left (correction_prod_le (primorial ⌊z⌋₊) d hd0) hnonneg
  simpa only [ite_div,zero_div] using h.trans hmul

end PrimePairCount
namespace PrimePairCount

lemma reciprocal_denominator_positive (d : ℕ) (hd : 2 ∣ d) (z : ℝ) (hz : 1 ≤ z) :
    0 < ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then ∏ p ∈ q.primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z) := by
  have hzpos : 0 < z := by linarith
  apply Finset.sum_pos'
  · intro q hq
    split_ifs
    · exact div_nonneg (pair_weight_nonneg q d hd) (by positivity)
    · simp
  · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by simpa using hz)⟩, ?_⟩
    simp only [squarefree_one,if_true,Nat.primeFactors_one,Finset.prod_empty,Nat.cast_one]
    positivity

lemma base_denominator_eq_shift_two (z : ℝ) :
    (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then ∏ p ∈ q.primeFactors,
        if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)) =
    (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
      (if Squarefree q then ∏ p ∈ q.primeFactors,
        if p ∣ 2 then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)) := by
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  split_ifs
  · apply Finset.prod_congr rfl
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hiff : p ∣ 2 ↔ p = 2 := Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two
    simp only [hiff]
    split_ifs with h
    · subst p; norm_num
    · rfl
  · rfl

lemma weighted_denominator_normalize (N : ℕ) (z : ℝ) (hz : 0 < z)
    (hNz : (N : ℝ) = 16*z^2) (g : ℕ → ℝ) (Q : Finset ℕ) :
    (∑ q ∈ Q, g q / ((N : ℝ)+16*(q : ℝ)*z)) =
      (∑ q ∈ Q, g q / (1+(q : ℝ)/z)) / N := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hNz]
  have hd : z+(q : ℝ) ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg q))
  have he : 16*z^2+16*(q : ℝ)*z = 16*z*(z+(q : ℝ)) := by ring
  rw [he]
  field_simp [ne_of_gt hz, hd]
  <;> ring

end PrimePairCount
namespace PrimePairCount

theorem prime_pair_count_base_denominator
    (hSieve : ∀ (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)),
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹)
    (hComp : ∀ (P d : ℕ) (hP : Squarefree P) (hd : 2 ∣ d)
    (F : ℕ → ℝ) (hF : Antitone F),
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) * F n) ≤
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p ∣ d then (1 : ℝ) / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) * F n) *
      ∏ p ∈ P.primeFactors,
        if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1)
    (x d : ℕ) (hd0 : 0 < d) (hd : 2 ∣ d) (z : ℝ) (hz : 1 ≤ z)
    (hscale : (x : ℝ) = 16*z^2) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤
    ((∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1) * x) /
      (∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)) + z + 1 := by
  classical
  let S : ℝ := ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
    (if Squarefree q then ∏ p ∈ q.primeFactors,
      if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)
  let B : ℝ := ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
    (if Squarefree q then ∏ p ∈ q.primeFactors,
      if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) / (1+(q : ℝ)/z)
  let K : ℝ := ∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1
  have hzpos : 0 < z := by linarith
  have hxpos : 0 < (x : ℝ) := by rw [hscale]; positivity
  have hS : 0 < S := reciprocal_denominator_positive d hd z hz
  have hB : 0 < B := by
    dsimp only [B]
    rw [base_denominator_eq_shift_two]
    exact reciprocal_denominator_positive 2 (dvd_refl 2) z hz
  have hc : B ≤ S*K := base_denominator_le hComp d hd0 hd z hz
  have hdiv : (x : ℝ)/S ≤ K*x/B := by
    apply (div_le_div_iff₀ hS hB).mpr
    calc
      (x : ℝ)*B ≤ (x : ℝ)*(S*K) := mul_le_mul_of_nonneg_left hc hxpos.le
      _ = _ := by ring
  have hcount := prime_pair_count_reciprocal hSieve x d hd0 hd z hz
  rw [weighted_denominator_normalize x z hzpos hscale] at hcount
  change (∑ n ∈ Finset.range (x+1),
    if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤
    (S/(x : ℝ))⁻¹ + z + 1 at hcount
  rw [inv_div] at hcount
  change (∑ n ∈ Finset.range (x+1),
    if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤ K*x/B+z+1
  linarith

end PrimePairCount

theorem solution
    (x d : ℕ) (hx : 16 ≤ x) (hd0 : 0 < d) (hd : 2 ∣ d) :
    (∑ n ∈ Finset.range (x+1),
      if Nat.Prime n ∧ Nat.Prime (n+d) ∧ n+d ≤ x then (1 : ℝ) else 0) ≤
    ((∏ p ∈ d.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1) * x) /
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt (x : ℝ)/4⌋₊,
        (if Squarefree q then ∏ p ∈ q.primeFactors,
          if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2) else 0) /
            (1+(q : ℝ)/(Real.sqrt (x : ℝ)/4))) + Real.sqrt (x : ℝ)/4 + 1 := by
  have hxR : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hsq := Real.sq_sqrt (Nat.cast_nonneg x)
  have hspos := Real.sqrt_nonneg (x : ℝ)
  have hz : 1 ≤ Real.sqrt (x : ℝ)/4 := by nlinarith
  have hscale : (x : ℝ) = 16*(Real.sqrt (x : ℝ)/4)^2 := by nlinarith
  exact PrimePairCount.prime_pair_count_base_denominator
    PrimePairSieve_reciprocal_weighted_sifted_bound
    PrimePairSieve.divisor_kernel_comparison x d hd0 hd _ hz hscale
