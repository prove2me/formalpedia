-- Prove2me | solution 1 for SchinzelHypothesisH.schinzelCondition_of_small_primes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T20:53:30.880836+00:00
-- url     : https://prove2.me/submissions/a234a808-ead6-45d8-9513-57e787ed8c88

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


theorem hyp_H_linear (a b : ℤ) (ha : 0 < a) (hab : IsCoprime a b) :
    {n : ℕ | (a * (n : ℤ) + b).natAbs.Prime}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  set q : ℕ := a.toNat with hq
  have hqa : (q : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hqa
    simp at hqa
    omega
  have hcop : IsCoprime b (q : ℤ) := by rw [hqa]; exact hab.symm
  obtain ⟨p, hpM, hpp, hpeq⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq ((a * (N : ℤ) + b).toNat + 1) hq0 hcop
  rw [Int.modEq_iff_dvd] at hpeq
  rw [hqa] at hpeq
  obtain ⟨k, hk⟩ := hpeq
  have hpe : (p : ℤ) = a * (-k) + b := by linear_combination -hk
  have hNlt : (a * (N : ℤ) + b) < (p : ℤ) := by
    have h1 : (a * (N : ℤ) + b) ≤ (((a * (N : ℤ) + b).toNat : ℕ) : ℤ) := Int.self_le_toNat _
    have h2 : (((a * (N : ℤ) + b).toNat + 1 : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hpM
    push_cast at h2
    linarith
  rw [hpe] at hNlt
  have h3 : a * (N : ℤ) < a * (-k) := by linarith
  have hmN : (N : ℤ) < -k := lt_of_mul_lt_mul_left h3 ha.le
  have hm0 : 0 ≤ -k := le_trans (Int.natCast_nonneg N) hmN.le
  have hnm : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg hm0
  have hmem : (-k).toNat ∈ {n : ℕ | (a * (n : ℤ) + b).natAbs.Prime} := by
    show (a * (((-k).toNat : ℕ) : ℤ) + b).natAbs.Prime
    rw [hnm, ← hpe, Int.natAbs_natCast]
    exact hpp
  have hle : ((-k).toNat : ℕ) ≤ N := hN hmem
  have hle' : (((-k).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
  rw [hnm] at hle'
  linarith



theorem schinzel_of_small (fs : Finset (Polynomial ℤ))
    (hB : ∀ f ∈ fs, BunyakovskyCondition f)
    (h : ∀ p : ℕ, p.Prime → p ≤ ∑ f ∈ fs, f.natDegree →
      ∃ n : ℤ, ¬ ((p : ℤ) ∣ ∏ f ∈ fs, f.eval n)) :
    SchinzelCondition fs := by
  intro p hp
  by_cases hle : p ≤ ∑ f ∈ fs, f.natDegree
  · exact h p hp hle
  push Not at hle
  have : Fact p.Prime := ⟨hp⟩
  set F : Polynomial ℤ := ∏ f ∈ fs, f with hF
  have hFprim : F.IsPrimitive := by
    rw [hF]
    refine Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) ?_ ?_
    · exact monic_one.isPrimitive
    · intro f hf
      exact ((hB f hf).2.2).isPrimitive (by have := (hB f hf).1; omega)
  have hdeg : F.natDegree = ∑ f ∈ fs, f.natDegree :=
    Polynomial.natDegree_prod _ _ (fun f hf => ((hB f hf).2.2).ne_zero)
  set G : Polynomial (ZMod p) := F.map (Int.castRingHom (ZMod p)) with hG
  have hGne : G ≠ 0 := by
    intro h0
    have hcoeff : ∀ i, (p : ℤ) ∣ F.coeff i := by
      intro i
      have hc : (F.map (Int.castRingHom (ZMod p))).coeff i = 0 := by rw [← hG, h0]; simp
      rw [Polynomial.coeff_map] at hc
      have : ((F.coeff i : ℤ) : ZMod p) = 0 := hc
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
    have hdvd : (C (p : ℤ)) ∣ F := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 hcoeff
    have hunit := hFprim _ hdvd
    rw [Int.isUnit_iff] at hunit
    have h2 := hp.two_le
    omega
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, ¬ G.IsRoot r := by
    by_contra hc
    push Not at hc
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ G.roots.toFinset := by
      intro r _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hGne]
      exact hc r
    have h1 : Fintype.card (ZMod p) ≤ G.roots.toFinset.card := by
      simpa using Finset.card_le_card hsub
    have h2 : G.roots.toFinset.card ≤ Multiset.card G.roots := G.roots.toFinset_card_le
    have h3 : Multiset.card G.roots ≤ G.natDegree := Polynomial.card_roots' G
    have h4 : G.natDegree ≤ F.natDegree := by rw [hG]; exact Polynomial.natDegree_map_le
    rw [ZMod.card] at h1
    omega
  refine ⟨((r.val : ℕ) : ℤ), ?_⟩
  intro hdvd
  apply hr
  have hprod : (∏ f ∈ fs, f.eval ((r.val : ℕ) : ℤ)) = F.eval ((r.val : ℕ) : ℤ) := by
    rw [hF, Polynomial.eval_prod]
  rw [hprod] at hdvd
  have hz : ((F.eval ((r.val : ℕ) : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
  have hlift : ((((r.val : ℕ) : ℤ)) : ZMod p) = r := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  show G.eval r = 0
  rw [← hlift, hG, Polynomial.eval_intCast_map]
  simpa using hz


end SchLoc

open Polynomial SchinzelHypothesisH in
theorem solution (fs : Finset (Polynomial ℤ))
    (hB : ∀ f ∈ fs, BunyakovskyCondition f)
    (h : ∀ p : ℕ, p.Prime → p ≤ ∑ f ∈ fs, f.natDegree →
      ∃ n : ℤ, ¬ ((p : ℤ) ∣ ∏ f ∈ fs, f.eval n)) :
    SchinzelCondition fs :=
  SchLoc.schinzel_of_small fs hB h
