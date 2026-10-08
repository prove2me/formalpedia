-- Prove2me | solution 1 for SkutellaCQP.NoRel.cqp_psd
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:15:31.557795+00:00
-- url     : https://prove2.me/submissions/ad29f444-1118-43ed-892c-c063e8c65e8e

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

open Finset SkutellaCQP.NoRel

private lemma min_kernel {A : Type} [DecidableEq A] (s : Finset A)
    (r x : A → ℝ) (hr : ∀ j ∈ s, 0 ≤ r j) :
    0 ≤ ∑ j ∈ s, ∑ k ∈ s, x j * x k * min (r j) (r k) := by
  revert r
  refine Finset.strongInductionOn s ?_
  intro s ih r hr
  by_cases hs : s = ∅
  · simp [hs]
  obtain ⟨a, ha, hmin⟩ := exists_min_image s r (nonempty_iff_ne_empty.mpr hs)
  let t := s.erase a
  let r' := fun j => r j - r a
  have ht : t ⊂ s := erase_ssubset ha
  have hpos : ∀ j ∈ t, 0 ≤ r' j := fun j hj =>
    sub_nonneg.mpr (hmin j (mem_erase.mp hj).2)
  have hrec := ih t ht r' hpos
  have he : ∑ j ∈ s, ∑ k ∈ s, x j * x k * min (r' j) (r' k) =
      ∑ j ∈ t, ∑ k ∈ t, x j * x k * min (r' j) (r' k) := by
    have hins : insert a t = s := insert_erase ha
    rw [← hins, sum_insert (by simp [t])]
    have hzero : ∀ j ∈ s, min (r' a) (r' j) = 0 ∧ min (r' j) (r' a) = 0 := by
      intro j hj
      have hp : 0 ≤ r' j := sub_nonneg.mpr (hmin j hj)
      simp [r', min_eq_left hp, min_eq_right hp]
    have hz : (∑ k ∈ insert a t, x a * x k * min (r' a) (r' k)) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [(hzero k (hins ▸ hk)).1, mul_zero]
    rw [hz, zero_add]
    apply sum_congr rfl
    intro j hj
    rw [sum_insert (by simp [t]), (hzero j (mem_erase.mp hj).2).2]
    simp
  have hsplit :
      (∑ j ∈ s, ∑ k ∈ s, x j * x k * min (r j) (r k)) =
      r a * (∑ j ∈ s, x j) ^ 2 +
      ∑ j ∈ s, ∑ k ∈ s, x j * x k * min (r' j) (r' k) := by
    simp only [r', min_sub_sub_right, mul_sub, sum_sub_distrib]
    have heq : (∑ j ∈ s, ∑ k ∈ s, x j * x k * r a) =
        r a * (∑ j ∈ s, x j) ^ 2 := by
      simp only [← sum_mul, ← mul_sum]
      ring
    rw [heq]
    ring
  rw [hsplit, he]
  exact add_nonneg (mul_nonneg (hr a ha) (sq_nonneg _)) hrec

private lemma entry {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (x y : Fin m × Fin n) :
    (Dmat p w + Matrix.diagonal (cvec p w)) x y =
      if x.1 = y.1 then p x.1 x.2 * p y.1 y.2 *
        min (w x.2 / p x.1 x.2) (w y.2 / p y.1 y.2) else 0 := by
  by_cases hi : x.1 = y.1
  · rcases x with ⟨i,j⟩
    rcases y with ⟨h,k⟩
    dsimp at hi
    subst h
    by_cases hj : j = k
    · subst k
      simp [Dmat, cvec]
      field_simp [ne_of_gt (hp i j)] <;> ring
    have hd : (i,j) ≠ (i,k) := by simp [hj]
    simp only [Matrix.add_apply, Dmat, cvec, Matrix.diagonal_apply, hd, if_false,
      ne_eq, hj, false_or, not_false_eq_true, if_true, add_zero, Prod.fst, Prod.snd,
      not_true_eq_false, or_self]
    have hr : w j / p i j ≤ w k / p i k ↔ w j * p i k ≤ w k * p i j :=
      div_le_div_iff₀ (hp i j) (hp i k)
    by_cases hh : prec p w i k j
    · rw [if_pos hh, min_eq_left (hr.mpr (by rcases hh with hh | hh; linarith; linarith [hh.1]))]
      field_simp [ne_of_gt (hp i j), ne_of_gt (hp i k)] <;> ring
    · have hh' : prec p w i j k := by
        unfold prec at *
        rcases lt_trichotomy (w j * p i k) (w k * p i j) with hlt | heq | hgt
        · exact (hh (Or.inl hlt)).elim
        · exact Or.inr ⟨heq, lt_of_le_of_ne (le_of_not_gt (fun h => hh (Or.inr ⟨heq.symm,h⟩))) hj⟩
        · exact Or.inl hgt
      rw [if_neg hh, if_pos hh', min_eq_right (by
        rw [div_le_div_iff₀ (hp i k) (hp i j)]
        rcases hh' with hh' | hh'; linarith; linarith [hh'.1])]
      field_simp [ne_of_gt (hp i j), ne_of_gt (hp i k)] <;> ring
  · have hxy : x ≠ y := fun h => hi (congrArg Prod.fst h)
    simp [Dmat, Matrix.diagonal_apply, hxy, hi]

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    (Dmat p w + Matrix.diagonal (cvec p w)).PosSemidef := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext x y
    simp only [Matrix.conjTranspose_apply, star_trivial, entry p w hp]
    by_cases hi : x.1 = y.1
    · rw [if_pos hi, if_pos hi.symm, min_comm]
      ring
    · simp [hi, Ne.symm hi]
  · intro x
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      entry p w hp, Fintype.sum_prod_type, Prod.fst, Prod.snd, ite_mul, zero_mul,
      sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true]
    have he : (∑ i, ∑ j, x (i,j) * ∑ k,
        p i j * p i k * min (w j / p i j) (w k / p i k) * x (i,k)) =
        ∑ i, ∑ j, ∑ k, (x (i,j) * p i j) * (x (i,k) * p i k) *
          min (w j / p i j) (w k / p i k) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    rw [he]
    apply sum_nonneg
    intro i _
    exact min_kernel univ (fun j => w j / p i j) (fun j => x (i,j) * p i j)
      (fun j _ => div_nonneg (hw j) (hp i j).le)

#print axioms solution
