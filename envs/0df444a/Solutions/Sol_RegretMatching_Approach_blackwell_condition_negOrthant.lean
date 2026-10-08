-- Prove2me | solution 1 for RegretMatching.Approach.blackwell_condition_negOrthant
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:51:10.430541+00:00
-- url     : https://prove2.me/submissions/85905cd7-9843-4cc4-a3db-270f332f8247

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open RegretMatching.Approach
open Finset

private theorem offDiag_sum {A : Type} [Fintype A] [DecidableEq A]
    (lam : OffDiag A → ℝ) (v : A → A → ℝ) :
    (∑ l : OffDiag A, lam l * v l.1.1 l.1.2) =
    ∑ j : A, ∑ k : A, lamMat lam j k * v j k := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun p : A × A => p.1 ≠ p.2)
    (fun p => lamMat lam p.1 p.2 * v p.1 p.2)
  have hz : (∑ p : {p : A × A // ¬ p.1 ≠ p.2},
      lamMat lam p.1.1 p.1.2 * v p.1.1 p.1.2) = 0 := by
    apply sum_eq_zero
    intro p hp
    simp [lamMat, not_not.mp p.2]
  rw [hz, add_zero] at hs
  have he : (∑ p : OffDiag A, lamMat lam p.1.1 p.1.2 * v p.1.1 p.1.2) =
      ∑ p : OffDiag A, lam p * v p.1.1 p.1.2 := by
    apply sum_congr rfl
    intro p hp
    simp [lamMat, p.2]
  rw [he] at hs
  simpa [Fintype.sum_prod_type] using hs

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (lam : EuclideanSpace ℝ (OffDiag (S i))) (hlam : ∀ l, 0 ≤ lam l)
    (q : S i → ℝ) (hq : q ∈ stdSimplex ℝ (S i))
    (h35 : ∀ j : S i, ∑ k : S i, q k * lamMat (fun l => lam l) k j
      = q j * ∑ k : S i, lamMat (fun l => lam l) j k) :
    ∀ s : ∀ i, S i, inner ℝ lam (∑ a : S i, q a • vecPay u i a s) = 0 := by
  classical
  intro s
  let v := fun j : S i => u i (Function.update s i j)
  have coord (l : OffDiag (S i)) :
      (∑ a : S i, q a • vecPay u i a s) l = q l.1.1 * (v l.1.2 - v l.1.1) := by
    simp [vecPay, v, mul_ite]
  rw [PiLp.inner_apply]
  simp only [coord, RCLike.inner_apply, conj_trivial]
  have hre : (∑ l : OffDiag (S i), q l.1.1 * (v l.1.2 - v l.1.1) * lam l) =
      ∑ j : S i, ∑ k : S i, q j * lamMat (fun l => lam l) j k * (v k - v j) := by
    convert offDiag_sum (fun l => lam l) (fun j k => q j * (v k - v j)) using 1
    · apply sum_congr rfl; intro l hl; ring
    · apply sum_congr rfl; intro j hj
      apply sum_congr rfl; intro k hk; ring
  rw [hre]
  simp only [mul_sub, sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← sum_mul, h35, mul_sum, sum_mul]
#print axioms solution
