-- Prove2me | solution 1 for WeierstrassEllipticZeta.cleared_auxiliary_polynomial_presentation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T13:38:16.61564+00:00
-- url     : https://prove2.me/submissions/e18fd2bd-0e5a-4f91-97b4-4474d28333c9

import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section
open MvPolynomial
open scoped Pointwise

open WeierstrassEllipticZeta

private def p2m_blockBound (P : MvPolynomial (Fin 4) ℂ) (a b : ℕ) : Prop :=
  ∀ d ∈ P.support, d 0 ≤ a ∧ d 1 + d 2 + d 3 ≤ b

private lemma p2m_block_mono {P : MvPolynomial (Fin 4) ℂ} {a b a' b' : ℕ}
    (h : p2m_blockBound P a b) (ha : a ≤ a') (hb : b ≤ b') : p2m_blockBound P a' b' :=
  fun d hd => ⟨(h d hd).1.trans ha, (h d hd).2.trans hb⟩

private lemma p2m_block_add {P Q : MvPolynomial (Fin 4) ℂ} {a b : ℕ}
    (hP : p2m_blockBound P a b) (hQ : p2m_blockBound Q a b) : p2m_blockBound (P + Q) a b := by
  intro d hd
  rcases Finset.mem_union.mp (support_add hd) with hd | hd
  · exact hP d hd
  · exact hQ d hd

private lemma p2m_block_sub {P Q : MvPolynomial (Fin 4) ℂ} {a b : ℕ}
    (hP : p2m_blockBound P a b) (hQ : p2m_blockBound Q a b) : p2m_blockBound (P - Q) a b := by
  rw [sub_eq_add_neg]
  apply p2m_block_add hP
  simpa only [p2m_blockBound, support_neg] using hQ

private lemma p2m_block_mul {P Q : MvPolynomial (Fin 4) ℂ} {a b a' b' : ℕ}
    (hP : p2m_blockBound P a b) (hQ : p2m_blockBound Q a' b') :
    p2m_blockBound (P * Q) (a + a') (b + b') := by
  intro d hd
  obtain ⟨e, he, f, hf, rfl⟩ := Finset.mem_add.mp (support_mul P Q hd)
  obtain ⟨h₀, h₁⟩ := hP e he
  obtain ⟨h₂, h₃⟩ := hQ f hf
  simp only [Finsupp.add_apply]
  omega

private lemma p2m_block_C (c : ℂ) : p2m_blockBound (C c) 0 0 := by
  intro d hd
  have hd' : d = 0 := Finset.mem_singleton.mp (support_monomial_subset hd)
  subst d
  simp

private lemma p2m_block_pow {P : MvPolynomial (Fin 4) ℂ} {a b : ℕ}
    (hP : p2m_blockBound P a b) (n : ℕ) : p2m_blockBound (P ^ n) (n * a) (n * b) := by
  induction n with
  | zero => simpa using p2m_block_C (1 : ℂ)
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using p2m_block_mul ih hP

private lemma p2m_block_sum {ι : Type*} [Fintype ι] (P : ι → MvPolynomial (Fin 4) ℂ)
    {a b : ℕ} (hP : ∀ i, p2m_blockBound (P i) a b) : p2m_blockBound (∑ i, P i) a b := by
  classical
  intro d hd
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (support_sum hd)
  exact hP i d hi

private lemma p2m_block_X (i : Fin 4) :
    p2m_blockBound (X i) (if i = 0 then 1 else 0) (if i = 0 then 0 else 1) := by
  intro d hd
  rw [support_X, Finset.mem_singleton] at hd
  subst d
  fin_cases i <;> norm_num [Finsupp.single_apply, Fin.ext_iff]

theorem solution
    (L : PeriodPair) (v : ℂ) (hv : v ∉ L.lattice) (m l : ℕ)
    (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ) :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      (∀ d ∈ P.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ 5 * l) ∧
      ∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        MvPolynomial.eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z] P =
          (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * l) *
            (∑ i, c i * (z + v) ^ i.1.val * L.weierstrassP (z + v) ^ i.2.1.val *
              weierstrassZeta L (z + v) ^ i.2.2.val) := by
  classical
  let A : MvPolynomial (Fin 4) ℂ := C 2 * (C (L.weierstrassP v) - X 1)
  let B : MvPolynomial (Fin 4) ℂ :=
    C (-4) * (X 1 + C (L.weierstrassP v)) * (C (L.weierstrassP v) - X 1) ^ 2 +
      (C (L.derivWeierstrassP v) - X 2) ^ 2
  let E : MvPolynomial (Fin 4) ℂ :=
    C 2 * (X 3 + C (weierstrassZeta L v)) * (C (L.weierstrassP v) - X 1) +
      (C (L.derivWeierstrassP v) - X 2)
  let P : MvPolynomial (Fin 4) ℂ := ∑ i, C (c i) * (X 0 + C v) ^ i.1.val *
    A ^ (3 * l - 2 * i.2.1.val - i.2.2.val) * B ^ i.2.1.val * E ^ i.2.2.val
  have hX₀ : p2m_blockBound (X 0) 1 0 := by simpa using p2m_block_X 0
  have hX₁ : p2m_blockBound (X 1) 0 1 := by simpa using p2m_block_X 1
  have hX₂ : p2m_blockBound (X 2) 0 1 := by simpa using p2m_block_X 2
  have hX₃ : p2m_blockBound (X 3) 0 1 := by simpa using p2m_block_X 3
  have hconst (a : ℂ) : p2m_blockBound (C a) 0 1 :=
    p2m_block_mono (p2m_block_C a) le_rfl (by omega)
  have hdiff : p2m_blockBound (C (L.weierstrassP v) - X 1) 0 1 :=
    p2m_block_sub (hconst _) hX₁
  have hderiv : p2m_blockBound (C (L.derivWeierstrassP v) - X 2) 0 1 :=
    p2m_block_sub (hconst _) hX₂
  have hA : p2m_blockBound A 0 1 := by
    simpa [A] using p2m_block_mul (p2m_block_C 2) hdiff
  have hB : p2m_blockBound B 0 3 := by
    apply p2m_block_add
    · simpa using p2m_block_mul (p2m_block_mul (p2m_block_C (-4)) (p2m_block_add hX₁ (hconst _)))
        (p2m_block_pow hdiff 2)
    · exact p2m_block_mono (p2m_block_pow hderiv 2) (by omega) (by omega)
  have hE : p2m_blockBound E 0 2 := by
    apply p2m_block_add
    · simpa using p2m_block_mul (p2m_block_mul (p2m_block_C 2) (p2m_block_add hX₃ (hconst _))) hdiff
    · exact p2m_block_mono hderiv le_rfl (by omega)
  have hshift : p2m_blockBound (X 0 + C v) 1 0 :=
    p2m_block_add hX₀ (p2m_block_mono (p2m_block_C v) (by omega) le_rfl)
  refine ⟨P, ?_, ?_⟩
  · apply p2m_block_sum
    intro i
    have hterm := p2m_block_mul (p2m_block_mul (p2m_block_mul
      (p2m_block_mul (p2m_block_C (c i)) (p2m_block_pow hshift i.1.val))
      (p2m_block_pow hA (3 * l - 2 * i.2.1.val - i.2.2.val)))
      (p2m_block_pow hB i.2.1.val)) (p2m_block_pow hE i.2.2.val)
    apply p2m_block_mono hterm
    · have hi := i.1.isLt
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
      omega
    · have hj := i.2.1.isLt
      have hk := i.2.2.isLt
      simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero]
      omega
  · intro z hz hzv
    have hZ := zeta_addition_formula L z v hz hv hzv
    have hW := wp_addition_formula L z v hz hv hzv
    dsimp only [P]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hnum : 4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 =
        (2 * (L.weierstrassP v - L.weierstrassP z)) ^ 2 := by ring
    have hexp : 3 * l = (3 * l - 2 * i.2.1.val - i.2.2.val) +
        2 * i.2.1.val + i.2.2.val := by
      have hj := i.2.1.isLt
      have hk := i.2.2.isLt
      omega
    simp only [map_mul, map_pow, map_add, map_sub, eval_C, eval_X, A, B, E,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [show 2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) =
        2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) by
      linear_combination -hZ, ← hW, hnum]
    conv_rhs => rw [hexp, pow_add, pow_add]
    simp only [mul_pow, ← pow_mul]
    ring

