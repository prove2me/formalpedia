-- Prove2me | solution 1 for SchinzelHypothesisH.bunyakovsky_of_hypothesis_H
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T20:47:50.993672+00:00
-- url     : https://prove2.me/submissions/431fd894-0fa2-46fa-ac99-79351bc324f3

import Definitions.Def_SchinzelHypothesisH_core

set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace SchLoc

open Polynomial SchinzelHypothesisH

/-! ### Reduction to a single polynomial -/

theorem primeValueSet_singleton (f : Polynomial ℤ) :
    PrimeValueSet ({f} : Finset (Polynomial ℤ)) = {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime} := by
  ext n; simp [PrimeValueSet]

theorem bunyakovsky_of_H
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite)
    (f : Polynomial ℤ) (hf : BunyakovskyCondition f)
    (hfix : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ f.eval n)) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by
  have hB : ∀ g ∈ ({f} : Finset (Polynomial ℤ)), BunyakovskyCondition g := by
    intro g hg
    rw [Finset.mem_singleton] at hg
    subst hg; exact hf
  have hS : SchinzelCondition ({f} : Finset (Polynomial ℤ)) := by
    intro p hp
    obtain ⟨n, hn⟩ := hfix p hp
    exact ⟨n, by simpa using hn⟩
  have h := H {f} hB hS
  rwa [primeValueSet_singleton] at h

/-! ### `n² + 1` -/

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : Polynomial ℤ) := by
  have hmonic : (X ^ 2 + 1 : Polynomial ℤ).Monic := by
    have : (X ^ 2 + 1 : Polynomial ℤ) = X ^ 2 + C 1 := by simp
    rw [this]
    exact monic_X_pow_add_C 1 (by norm_num)
  have hdeg : (X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by
    compute_degree!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [mem_roots hmonic.ne_zero] at hx
  have : x ^ 2 + 1 = 0 := by simpa [IsRoot] using hx
  nlinarith [sq_nonneg x]

theorem primes_sq_add_one_of_H
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite) :
    {n : ℕ | (n ^ 2 + 1).Prime}.Infinite := by
  have hB : BunyakovskyCondition (X ^ 2 + 1 : Polynomial ℤ) := by
    refine ⟨?_, ?_, irreducible_X_sq_add_one⟩
    · have : (X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by compute_degree!
      omega
    · have hmonic : (X ^ 2 + 1 : Polynomial ℤ).Monic := by
        have h : (X ^ 2 + 1 : Polynomial ℤ) = X ^ 2 + C 1 := by simp
        rw [h]; exact monic_X_pow_add_C 1 (by norm_num)
      rw [hmonic.leadingCoeff]; norm_num
  have hfix : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : Polynomial ℤ).eval n) := by
    intro p hp
    refine ⟨0, ?_⟩
    simp only [eval_add, eval_pow, eval_X, eval_one]
    intro hd
    rw [show ((0 : ℤ) ^ 2 + 1) = 1 by norm_num] at hd
    have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hd
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    omega
  have h := bunyakovsky_of_H H _ hB hfix
  have hset : {n : ℕ | ((X ^ 2 + 1 : Polynomial ℤ).eval (n : ℤ)).natAbs.Prime}
      = {n : ℕ | (n ^ 2 + 1).Prime} := by
    ext n
    simp only [Set.mem_ofPred, eval_add, eval_pow, eval_X, eval_one]
    have hnat : ((n : ℤ) ^ 2 + 1).natAbs = n ^ 2 + 1 := by
      rw [show ((n : ℤ) ^ 2 + 1) = ((n ^ 2 + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
    rw [hnat]
  rwa [hset] at h

/-! ### Twin primes -/

theorem X_ne_X_add_two : (X : Polynomial ℤ) ≠ X + C 2 := by
  intro h
  have := congrArg (fun q => Polynomial.coeff q 0) h
  simp at this

theorem twin_primes_of_H
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite) :
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite := by
  have hmonic : (X + C 2 : Polynomial ℤ).Monic := monic_X_add_C 2
  have hB : ∀ f ∈ ({X, X + C 2} : Finset (Polynomial ℤ)), BunyakovskyCondition f := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact ⟨by simp, by simp, irreducible_X⟩
    · refine ⟨?_, ?_, hmonic.irreducible_of_degree_eq_one (degree_X_add_C 2)⟩
      · rw [natDegree_X_add_C]
      · rw [hmonic.leadingCoeff]; norm_num
  have hprod : ∀ n : ℤ, (∏ f ∈ ({X, X + C 2} : Finset (Polynomial ℤ)), f.eval n)
      = n * (n + 2) := by
    intro n
    rw [Finset.prod_pair X_ne_X_add_two]
    simp
  have hS : SchinzelCondition ({X, X + C 2} : Finset (Polynomial ℤ)) := by
    intro p hp
    by_cases h3 : p = 3
    · refine ⟨2, ?_⟩
      rw [hprod, h3]
      norm_num
    · refine ⟨1, ?_⟩
      rw [hprod]
      norm_num
      intro hd
      have : p ∣ 3 := by exact_mod_cast hd
      have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 this
      exact h3 this
  have h := H _ hB hS
  have hset : PrimeValueSet ({X, X + C 2} : Finset (Polynomial ℤ))
      = {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
    ext n
    simp only [PrimeValueSet, Set.mem_ofPred, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, eval_add, eval_X, eval_C]
    have h1 : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
    have h2 : ((n : ℤ) + 2).natAbs = n + 2 := by
      rw [show ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
    rw [h1, h2]
  rwa [hset] at h

/-! ### A fixed prime divisor makes the prime-value set finite -/

theorem finite_pvs (fs : Finset (Polynomial ℤ))
    (hB : ∀ f ∈ fs, BunyakovskyCondition f) (hS : ¬ SchinzelCondition fs) :
    (PrimeValueSet fs).Finite := by
  rw [SchinzelCondition] at hS
  push Not at hS
  obtain ⟨p, hp, hdvd⟩ := hS
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hfin : ∀ f ∈ fs,
      ({n : ℕ | f.eval (n : ℤ) = (p : ℤ) ∨ f.eval (n : ℤ) = -(p : ℤ)}).Finite := by
    intro f hf
    have hdeg : 1 ≤ f.natDegree := (hB f hf).1
    have hne1 : f - C (p : ℤ) ≠ 0 := by
      intro h
      have : f = C (p : ℤ) := by linear_combination (norm := ring_nf) h
      rw [this, natDegree_C] at hdeg
      omega
    have hne2 : f + C (p : ℤ) ≠ 0 := by
      intro h
      have : f = C (-(p : ℤ)) := by rw [map_neg]; linear_combination (norm := ring_nf) h
      rw [this, natDegree_C] at hdeg
      omega
    have hr1 := Polynomial.finite_setOfPred_isRoot hne1
    have hr2 := Polynomial.finite_setOfPred_isRoot hne2
    have hunion : ({n : ℕ | f.eval (n : ℤ) = (p : ℤ) ∨ f.eval (n : ℤ) = -(p : ℤ)})
        ⊆ (fun n : ℕ => (n : ℤ)) ⁻¹'
            ({x : ℤ | (f - C (p : ℤ)).IsRoot x} ∪ {x : ℤ | (f + C (p : ℤ)).IsRoot x}) := by
      intro n hn
      rcases hn with h | h
      · exact Or.inl (by simp [IsRoot, h])
      · exact Or.inr (by simp [IsRoot, h])
    refine Set.Finite.subset (Set.Finite.preimage ?_ (hr1.union hr2)) hunion
    exact fun a _ b _ hab => by exact_mod_cast hab
  refine Set.Finite.subset (Set.Finite.biUnion fs.finite_toSet hfin) ?_
  intro n hn
  have hn' : ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime := hn
  obtain ⟨f, hf, hfd⟩ := (Prime.dvd_finsetProd_iff hpZ _).1 (hdvd (n : ℤ))
  refine Set.mem_biUnion hf ?_
  have hpnat : p ∣ (f.eval (n : ℤ)).natAbs := by
    have := Int.natAbs_dvd_natAbs.2 hfd
    simpa using this
  have heq : (f.eval (n : ℤ)).natAbs = p :=
    ((Nat.prime_dvd_prime_iff_eq hp (hn' f hf)).1 hpnat).symm
  rcases Int.natAbs_eq_iff.1 heq with h | h
  · exact Or.inl h
  · exact Or.inr h

end SchLoc

open Polynomial SchinzelHypothesisH in
theorem solution
    (H : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, BunyakovskyCondition f) →
      SchinzelCondition fs → (PrimeValueSet fs).Infinite)
    (f : Polynomial ℤ) (hf : BunyakovskyCondition f)
    (hfix : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ ((p : ℤ) ∣ f.eval n)) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite :=
  SchLoc.bunyakovsky_of_H H f hf hfix
