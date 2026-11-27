-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.lemma_I_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:44.588949+00:00
-- url     : https://prove2.me/submissions/9a26d0ad-490c-4212-881c-68a9880c0737

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Supplement_LambdaMatrix

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

theorem solution (m n k : ℕ) (h : 0 < m + n + k) : (Lambda m n k).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext x y
    rcases x with i | p | j <;> rcases y with i' | p' | j' <;>
      simp [Lambda, Dmat, Jmat, Rmat, Qmat, Dtilde, Matrix.one_apply, eq_comm, mul_comm]
  · intro x hx
    have e11 : ∀ i i', Lambda m n k (.inl i) (.inl i') = 2 * (if i = i' then 1 else 0) + 2 := by
      intro i i'; simp [Lambda, Dmat, Jmat, Matrix.one_apply]; split_ifs <;> norm_num
    have e12 : ∀ i p, Lambda m n k (.inl i) (.inr (.inl p)) = if p.2 = 0 then 2 else 1 := by
      intro i p; simp [Lambda, Rmat]
    have e13 : ∀ i j, Lambda m n k (.inl i) (.inr (.inr j)) = 1 := by
      intro i j; simp [Lambda, Jmat]
    have e21 : ∀ p i, Lambda m n k (.inr (.inl p)) (.inl i) = if p.2 = 0 then 2 else 1 := by
      intro p i; simp [Lambda, Rmat]
    have e22 : ∀ p p', Lambda m n k (.inr (.inl p)) (.inr (.inl p')) =
        ((if p.1 = p'.1 then 1 else 0) + 1) * ((if p.2 = p'.2 then 1 else 0) + 1) := by
      intro p p'; simp [Lambda, Dtilde, Dmat, Jmat, Matrix.one_apply]
    have e23 : ∀ p j, Lambda m n k (.inr (.inl p)) (.inr (.inr j)) = if p.2 = 0 then 1 else 2 := by
      intro p j; simp [Lambda, Qmat]
    have e31 : ∀ j i, Lambda m n k (.inr (.inr j)) (.inl i) = 1 := by
      intro j i; simp [Lambda, Jmat]
    have e32 : ∀ j p, Lambda m n k (.inr (.inr j)) (.inr (.inl p)) = if p.2 = 0 then 1 else 2 := by
      intro j p; simp [Lambda, Qmat]
    have e33 : ∀ j j', Lambda m n k (.inr (.inr j)) (.inr (.inr j')) = 2 * (if j = j' then 1 else 0) + 2 := by
      intro j j'; simp [Lambda, Dmat, Jmat, Matrix.one_apply]; split_ifs <;> norm_num
    set a : Fin m → ℝ := fun i => x (.inl i) with ha
    set b : Fin k → Fin 2 → ℝ := fun l s => x (.inr (.inl (l, s))) with hb
    set c : Fin n → ℝ := fun j => x (.inr (.inr j)) with hc
    set A := ∑ i, a i with hA
    set B0 := ∑ l, b l 0 with hB0
    set B1 := ∑ l, b l 1 with hB1
    set C := ∑ j, c j with hC
    have hMa : ∀ i, (Matrix.mulVec (Lambda m n k) x) (.inl i) = 2 * a i + 2 * A + 2 * B0 + B1 + C := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, e11, e12, e13]
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum, ha, hb, hc, hA, hB0, hB1, hC]
      ring
    have hMc : ∀ j, (Matrix.mulVec (Lambda m n k) x) (.inr (.inr j)) = A + B0 + 2 * B1 + 2 * c j + 2 * C := by
      intro j
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, e31, e32, e33]
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum, ha, hb, hc, hA, hB0, hB1, hC]
      ring
    have hMb0 : ∀ l, (Matrix.mulVec (Lambda m n k) x) (.inr (.inl (l, 0))) =
        2 * A + 2 * b l 0 + 2 * B0 + b l 1 + B1 + C := by
      intro l
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, e21, e22, e23]
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum, ha, hb, hc, hA, hB0, hB1, hC]
      ring
    have hMb1 : ∀ l, (Matrix.mulVec (Lambda m n k) x) (.inr (.inl (l, 1))) =
        A + b l 0 + B0 + 2 * b l 1 + 2 * B1 + 2 * C := by
      intro l
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, e21, e22, e23]
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum, ha, hb, hc, hA, hB0, hB1, hC]
      ring
    have hq : dotProduct (star x) (Matrix.mulVec (Lambda m n k) x) =
        ∑ i, a i * (2 * a i + 2 * A + 2 * B0 + B1 + C)
        + ∑ l, (b l 0 * (2 * A + 2 * b l 0 + 2 * B0 + b l 1 + B1 + C)
            + b l 1 * (A + b l 0 + B0 + 2 * b l 1 + 2 * B1 + 2 * C))
        + ∑ j, c j * (A + B0 + 2 * B1 + 2 * c j + 2 * C) := by
      simp only [dotProduct, star_trivial, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
        hMa, hMb0, hMb1, hMc]
      simp only [ha, hb, hc]
      ring
    have ha' : ∑ i, a i * (2 * a i + 2 * A + 2 * B0 + B1 + C)
        = 2 * ∑ i, a i ^ 2 + A * (2 * A + 2 * B0 + B1 + C) := by
      have : ∀ i, a i * (2 * a i + 2 * A + 2 * B0 + B1 + C) = 2 * a i ^ 2 + a i * (2 * A + 2 * B0 + B1 + C) :=
        fun i => by ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [← hA]
    have hc' : ∑ j, c j * (A + B0 + 2 * B1 + 2 * c j + 2 * C)
        = 2 * ∑ j, c j ^ 2 + C * (A + B0 + 2 * B1 + 2 * C) := by
      have : ∀ j, c j * (A + B0 + 2 * B1 + 2 * c j + 2 * C) = 2 * c j ^ 2 + c j * (A + B0 + 2 * B1 + 2 * C) :=
        fun j => by ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [← hC]
    have hb' : ∑ l, (b l 0 * (2 * A + 2 * b l 0 + 2 * B0 + b l 1 + B1 + C)
            + b l 1 * (A + b l 0 + B0 + 2 * b l 1 + 2 * B1 + 2 * C))
        = ∑ l, (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2) + B0 * (2 * A + 2 * B0 + B1 + C)
          + B1 * (A + B0 + 2 * B1 + 2 * C) := by
      have : ∀ l, (b l 0 * (2 * A + 2 * b l 0 + 2 * B0 + b l 1 + B1 + C)
            + b l 1 * (A + b l 0 + B0 + 2 * b l 1 + 2 * B1 + 2 * C))
          = (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2) + b l 0 * (2 * A + 2 * B0 + B1 + C)
            + b l 1 * (A + B0 + 2 * B1 + 2 * C) := fun l => by ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [← hB0, ← hB1]
    rw [hq, ha', hb', hc']
    have Sa : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have Sc : 0 ≤ ∑ j, c j ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have Sb : 0 ≤ ∑ l, (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hbr : 0 ≤ A * (2 * A + 2 * B0 + B1 + C) + B0 * (2 * A + 2 * B0 + B1 + C)
          + B1 * (A + B0 + 2 * B1 + 2 * C) + C * (A + B0 + 2 * B1 + 2 * C) := by
      nlinarith [sq_nonneg (A + B0), sq_nonneg (B1 + C), sq_nonneg (A + B0 + B1 + C)]
    have hpos : 0 < ∑ i, a i ^ 2 ∨ 0 < ∑ l, (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2)
        ∨ 0 < ∑ j, c j ^ 2 := by
      obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
      rcases y with i | ⟨l, s⟩ | j
      · left
        have h1 : a i ^ 2 ≤ ∑ i, a i ^ 2 :=
          Finset.single_le_sum (f := fun i => a i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
        have h2 : 0 < a i ^ 2 := by
          have : a i ≠ 0 := hy
          positivity
        linarith
      · right; left
        have h1 : (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2) ≤ ∑ l, (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2) :=
          Finset.single_le_sum (f := fun l => (b l 0 ^ 2 + b l 1 ^ 2 + (b l 0 + b l 1) ^ 2))
            (fun i _ => by positivity) (Finset.mem_univ l)
        have h2 : 0 < b l s ^ 2 := by
          have : b l s ≠ 0 := hy
          positivity
        fin_cases s
        · simp only [Fin.zero_eta] at h2
          nlinarith [sq_nonneg (b l 1), sq_nonneg (b l 0 + b l 1)]
        · simp only [Fin.mk_one] at h2
          nlinarith [sq_nonneg (b l 0), sq_nonneg (b l 0 + b l 1)]
      · right; right
        have h1 : c j ^ 2 ≤ ∑ j, c j ^ 2 :=
          Finset.single_le_sum (f := fun j => c j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
        have h2 : 0 < c j ^ 2 := by
          have : c j ≠ 0 := hy
          positivity
        linarith
    rcases hpos with hp | hp | hp <;> nlinarith
