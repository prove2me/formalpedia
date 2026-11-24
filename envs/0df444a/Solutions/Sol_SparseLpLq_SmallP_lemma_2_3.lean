-- Prove2me | solution 1 for SparseLpLq.SmallP.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:46:41.490495+00:00
-- url     : https://prove2.me/submissions/3debeed4-2726-4413-b9c1-469a4c40f661

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

set_option autoImplicit false

open scoped ENNReal Matrix

open SparseLpLq.SmallP

private lemma esymm_eval_eq {n : ℕ} (a b : Fin n → ℝ)
    (h : ∀ k ∈ Finset.Icc 1 n, ∑ j, a j ^ k = ∑ j, b j ^ k) :
    ∀ k, k ≤ n → MvPolynomial.aeval a (MvPolynomial.esymm (Fin n) ℝ k)
      = MvPolynomial.aeval b (MvPolynomial.esymm (Fin n) ℝ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [MvPolynomial.esymm_zero]
    have e := MvPolynomial.mul_esymm_eq_sum (Fin n) ℝ k
    have ea := congrArg (MvPolynomial.aeval a) e
    have eb := congrArg (MvPolynomial.aeval b) e
    simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast] at ea eb
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk0
    rw [ea, eb]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hx3 := Finset.HasAntidiagonal.mem_antidiagonal.1 hx1
    have hp : ∀ f : Fin n → ℝ, MvPolynomial.aeval f (MvPolynomial.psum (Fin n) ℝ x.2)
        = ∑ j, f j ^ x.2 := by
      intro f; simp [MvPolynomial.psum]
    rw [ih x.1 hx2 (by omega), hp, hp, h x.2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]

private lemma multiset_eq {n : ℕ} (a b : Fin n → ℝ)
    (h : ∀ k ∈ Finset.Icc 1 n, ∑ j, a j ^ k = ∑ j, b j ^ k) :
    Finset.univ.val.map a = Finset.univ.val.map b := by
  have hprod : ∀ f : Fin n → ℝ,
      ((Finset.univ.val.map f).map fun r => Polynomial.X + Polynomial.C r).prod
        = ∑ j ∈ Finset.range (n + 1),
            Polynomial.C (MvPolynomial.aeval f (MvPolynomial.esymm (Fin n) ℝ j))
              * Polynomial.X ^ (n - j) := by
    intro f
    rw [Multiset.prod_X_add_C_eq_sum_esymm]
    simp [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have heq : ((Finset.univ.val.map a).map fun r => Polynomial.X + Polynomial.C r).prod
      = ((Finset.univ.val.map b).map fun r => Polynomial.X + Polynomial.C r).prod := by
    rw [hprod, hprod]
    apply Finset.sum_congr rfl
    intro j hj
    rw [esymm_eval_eq a b h j (by simp at hj; omega)]
  have hneg : ∀ s : Multiset ℝ, (s.map fun r => Polynomial.X + Polynomial.C r).prod
      = ((s.map Neg.neg).map fun r => Polynomial.X - Polynomial.C r).prod := by
    intro s
    rw [Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [sub_eq_add_neg]
  rw [hneg, hneg] at heq
  have hr := congrArg Polynomial.roots heq
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem solution {n : ℕ} (a b : Fin n → ℝ) (ha : Monotone a) (hb : Monotone b)
    (h : ∀ k ∈ Finset.Icc 1 n, ∑ j, a j ^ k = ∑ j, b j ^ k) :
    a = b := by
  have hm := multiset_eq a b h
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hm
  exact List.ofFn_injective (hm.eq_of_sortedLE ha.sortedLE_ofFn hb.sortedLE_ofFn)
