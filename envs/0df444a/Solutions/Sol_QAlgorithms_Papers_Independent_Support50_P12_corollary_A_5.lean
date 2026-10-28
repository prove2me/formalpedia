-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.corollary_A_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:42:57.423758+00:00
-- url     : https://prove2.me/submissions/a9561c26-adca-42c7-8d8d-69ea8f4f5842

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

section CA5_helpers

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

noncomputable def CA5_phi (t : ℝ) : ℝ → ℝ := fun x : ℝ => if x = 0 then 0 else Real.rpow x t

lemma CA5_sp {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (t : ℝ) :
    supportPower X t = cfc (CA5_phi t) X := rfl

lemma CA5_phi_zero (t : ℝ) : CA5_phi t 0 = 0 := by simp [CA5_phi]

lemma CA5_phi_pos (t x : ℝ) (hx : x ≠ 0) : CA5_phi t x = x ^ t := by
  simp [CA5_phi, hx, Real.rpow_eq_pow]

lemma CA5_phi_nonneg (t x : ℝ) (hx : 0 ≤ x) : 0 ≤ CA5_phi t x := by
  by_cases h : x = 0
  · rw [h, CA5_phi_zero]
  · rw [CA5_phi_pos t x h]; exact Real.rpow_nonneg hx _

noncomputable def CA5_L (m a x y : ℝ) : ℝ := a * m ^ (a - 1) * x + (1 - a) * m ^ a * y

lemma CA5_L_eq (m a x y : ℝ) (hm : 0 < m) (hy : 0 < y) :
    m ^ a * y * (1 + a * (x / (m * y) - 1)) = CA5_L m a x y := by
  unfold CA5_L
  rw [Real.rpow_sub_one hm.ne']
  field_simp
  ring

lemma CA5_F_eq (m a x y : ℝ) (hm : 0 < m) (hy : 0 < y) (hx : 0 ≤ x) :
    x ^ a * y ^ (1 - a) = m ^ a * y * (1 + (x / (m * y) - 1)) ^ a := by
  rw [show 1 + (x / (m * y) - 1) = x / (m * y) by ring, Real.div_rpow hx (by positivity),
    Real.mul_rpow hm.le hy.le, Real.rpow_sub hy, Real.rpow_one]
  have h1 := Real.rpow_pos_of_pos hm a
  have h2 := Real.rpow_pos_of_pos hy a
  field_simp

lemma CA5_s_ge (m x y : ℝ) (hm : 0 < m) (hy : 0 < y) (hx : 0 ≤ x) : -1 ≤ x / (m * y) - 1 := by
  have := div_nonneg hx (by positivity : (0 : ℝ) ≤ m * y)
  linarith

lemma CA5_s_ne (m x y : ℝ) (hm : 0 < m) (hy : 0 < y) (hne : x ≠ m * y) : x / (m * y) - 1 ≠ 0 := by
  intro h
  apply hne
  have h' : x / (m * y) = 1 := by linarith
  rwa [div_eq_one_iff_eq (by positivity)] at h'

lemma CA5_pt1 (m a x y : ℝ) (hm : 0 < m) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    CA5_phi a x * CA5_phi (1 - a) y ≤ CA5_L m a x y := by
  have hL1 : 0 ≤ a * m ^ (a - 1) * x :=
    mul_nonneg (mul_nonneg ha0 (Real.rpow_nonneg hm.le _)) hx
  have hL2 : 0 ≤ (1 - a) * m ^ a * y :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hm.le _)) hy
  by_cases hx0 : x = 0
  · rw [hx0, CA5_phi_zero, zero_mul]; unfold CA5_L; linarith
  by_cases hy0 : y = 0
  · rw [hy0, CA5_phi_zero, mul_zero]; unfold CA5_L; linarith
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  rw [CA5_phi_pos _ _ hx0, CA5_phi_pos _ _ hy0, CA5_F_eq m a x y hm hyp hx, ← CA5_L_eq m a x y hm hyp]
  exact mul_le_mul_of_nonneg_left
    (rpow_one_add_le_one_add_mul_self (CA5_s_ge m x y hm hyp hx) ha0 ha1) (by positivity)

lemma CA5_pt1s (m a x y : ℝ) (hm : 0 < m) (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hne : x ≠ m * y) : CA5_phi a x * CA5_phi (1 - a) y < CA5_L m a x y := by
  have hL1 : 0 ≤ a * m ^ (a - 1) * x :=
    mul_nonneg (mul_nonneg ha0.le (Real.rpow_nonneg hm.le _)) hx
  have hL2 : 0 ≤ (1 - a) * m ^ a * y :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hm.le _)) hy
  by_cases hx0 : x = 0
  · have hyp : 0 < y := by
      rcases lt_or_eq_of_le hy with h | h
      · exact h
      · exact absurd (by rw [hx0, ← h, mul_zero]) hne
    have : 0 < (1 - a) * m ^ a * y :=
      mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hm _)) hyp
    rw [hx0, CA5_phi_zero, zero_mul]; unfold CA5_L; linarith
  by_cases hy0 : y = 0
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have : 0 < a * m ^ (a - 1) * x :=
      mul_pos (mul_pos ha0 (Real.rpow_pos_of_pos hm _)) hxp
    rw [hy0, CA5_phi_zero, mul_zero]; unfold CA5_L; linarith
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  rw [CA5_phi_pos _ _ hx0, CA5_phi_pos _ _ hy0, CA5_F_eq m a x y hm hyp hx, ← CA5_L_eq m a x y hm hyp]
  exact mul_lt_mul_of_pos_left
    (rpow_one_add_lt_one_add_mul_self (CA5_s_ge m x y hm hyp hx) (CA5_s_ne m x y hm hyp hne)
      ha0 ha1) (by positivity)

lemma CA5_pt2 (m a x y : ℝ) (hm : 0 < m) (ha : 1 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hS : x ≠ 0 → y ≠ 0) : CA5_L m a x y ≤ CA5_phi a x * CA5_phi (1 - a) y := by
  by_cases hx0 : x = 0
  · have : (1 - a) * m ^ a * y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (Real.rpow_nonneg hm.le _)) hy
    rw [hx0, CA5_phi_zero, zero_mul]; unfold CA5_L; rw [mul_zero, zero_add]; exact this
  have hy0 := hS hx0
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  rw [CA5_phi_pos _ _ hx0, CA5_phi_pos _ _ hy0, CA5_F_eq m a x y hm hyp hx, ← CA5_L_eq m a x y hm hyp]
  exact mul_le_mul_of_nonneg_left
    (one_add_mul_self_le_rpow_one_add (CA5_s_ge m x y hm hyp hx) ha) (by positivity)

lemma CA5_pt2s (m a x y : ℝ) (hm : 0 < m) (ha : 1 < a) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hS : x ≠ 0 → y ≠ 0) (hne : x ≠ m * y) :
    CA5_L m a x y < CA5_phi a x * CA5_phi (1 - a) y := by
  by_cases hx0 : x = 0
  · have hyp : 0 < y := by
      rcases lt_or_eq_of_le hy with h | h
      · exact h
      · exact absurd (by rw [hx0, ← h, mul_zero]) hne
    have : (1 - a) * m ^ a * y < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (Real.rpow_pos_of_pos hm _)) hyp
    rw [hx0, CA5_phi_zero, zero_mul]; unfold CA5_L; rw [mul_zero, zero_add]; exact this
  have hy0 := hS hx0
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  rw [CA5_phi_pos _ _ hx0, CA5_phi_pos _ _ hy0, CA5_F_eq m a x y hm hyp hx, ← CA5_L_eq m a x y hm hyp]
  exact mul_lt_mul_of_pos_left
    (one_add_mul_self_lt_rpow_one_add (CA5_s_ge m x y hm hyp hx) (CA5_s_ne m x y hm hyp hne) ha)
    (by positivity)

lemma CA5_sumL {I : Type} [Fintype I] (m a : ℝ) (x y : I → ℝ) (w : I → I → ℝ)
    (hrow : ∀ j, ∑ i, w j i = 1) (hcol : ∀ i, ∑ j, w j i = 1) :
    ∑ j, ∑ i, w j i * CA5_L m a (x j) (y i) =
      a * m ^ (a - 1) * ∑ j, x j + (1 - a) * m ^ a * ∑ i, y i := by
  unfold CA5_L
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hrow j, one_mul]
  · rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hcol i, one_mul]

lemma CA5_rhs (a A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    a * (A / B) ^ (a - 1) * A + (1 - a) * (A / B) ^ a * B = A ^ a * B ^ (1 - a) := by
  rw [Real.div_rpow hA.le hB.le, Real.div_rpow hA.le hB.le, Real.rpow_sub_one hA.ne',
    Real.rpow_sub_one hB.ne', Real.rpow_sub hB, Real.rpow_one]
  have h1 := Real.rpow_pos_of_pos hA a
  have h2 := Real.rpow_pos_of_pos hB a
  field_simp
  ring

lemma CA5_allzero {I : Type} [Fintype I] (x : I → ℝ) (hx : ∀ j, 0 ≤ x j) (h : ∑ j, x j = 0) :
    ∀ j, x j = 0 := by
  intro j
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hx j)).1 h j (Finset.mem_univ _)

lemma CA5_x_of_y {I : Type} [Fintype I] (x y : I → ℝ) (w : I → I → ℝ)
    (hrow : ∀ j, ∑ i, w j i = 1) (hS : ∀ j i, w j i ≠ 0 → x j ≠ 0 → y i ≠ 0)
    (hy : ∀ i, y i = 0) : ∀ j, x j = 0 := by
  intro j
  by_contra hx
  have : ∀ i, w j i = 0 := fun i => by
    by_contra hw; exact hS j i hw hx (hy i)
  have h1 := hrow j
  simp [this] at h1

/-- The scalar core. -/
lemma CA5_real {I : Type} [Fintype I] (x y : I → ℝ) (w : I → I → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hy : ∀ i, 0 ≤ y i) (hw : ∀ j i, 0 ≤ w j i)
    (hrow : ∀ j, ∑ i, w j i = 1) (hcol : ∀ i, ∑ j, w j i = 1) :
    (∀ a, 0 ≤ a → a ≤ 1 → ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) ≤
      (∑ j, x j) ^ a * (∑ i, y i) ^ (1 - a)) ∧
    ((∀ j i, w j i ≠ 0 → x j ≠ 0 → y i ≠ 0) → ∀ a, 1 ≤ a →
      (∑ j, x j) ^ a * (∑ i, y i) ^ (1 - a) ≤
        ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i))) ∧
    ((∀ j i, w j i ≠ 0 → x j ≠ 0 → y i ≠ 0) →
      ((∃ a : ℝ, 0 < a ∧ a ≠ 1 ∧ ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) =
        (∑ j, x j) ^ a * (∑ i, y i) ^ (1 - a)) ↔
        ∃ c : ℝ, 0 ≤ c ∧ ∀ j i, w j i ≠ 0 → x j = c * y i)) := by
  set A := ∑ j, x j with hAdef
  set B := ∑ i, y i with hBdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => hx j
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hy i
  have hT0 : ∀ a, 0 ≤ ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) := fun a =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw j i) (mul_nonneg (CA5_phi_nonneg _ _ (hx j)) (CA5_phi_nonneg _ _ (hy i)))
  have hTx : ∀ a, (∀ j, x j = 0) →
      ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) = 0 := by
    intro a h; simp [h, CA5_phi_zero]
  have hTy : ∀ a, (∀ i, y i = 0) →
      ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) = 0 := by
    intro a h; simp [h, CA5_phi_zero]
  have hEq : ∀ a, 0 < A → 0 < B →
      ∑ j, ∑ i, w j i * CA5_L (A / B) a (x j) (y i) = A ^ a * B ^ (1 - a) := by
    intro a hA hB
    rw [CA5_sumL _ _ x y w hrow hcol, ← hAdef, ← hBdef]
    exact CA5_rhs a A B hA hB
  refine ⟨?_, ?_, ?_⟩
  · intro a ha0 ha1
    by_cases hA : A = 0
    · rw [hTx a (CA5_allzero x hx hA)]
      exact mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)
    by_cases hB : B = 0
    · rw [hTy a (CA5_allzero y hy hB)]
      exact mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)
    have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
    rw [← hEq a hAp hBp]
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (CA5_pt1 _ a _ _ (div_pos hAp hBp) ha0 ha1 (hx j) (hy i)) (hw j i)
  · intro hS a ha
    have ha0 : a ≠ 0 := by linarith
    by_cases hB : B = 0
    · have hx0 := CA5_x_of_y x y w hrow hS (CA5_allzero y hy hB)
      have : A = 0 := by rw [hAdef]; simp [hx0]
      rw [this, Real.zero_rpow ha0, zero_mul]; exact hT0 a
    by_cases hA : A = 0
    · rw [hA, Real.zero_rpow ha0, zero_mul]; exact hT0 a
    have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
    have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
    rw [← hEq a hAp hBp]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
    by_cases hw0 : w j i = 0
    · simp [hw0]
    exact mul_le_mul_of_nonneg_left (CA5_pt2 _ a _ _ (div_pos hAp hBp) ha (hx j) (hy i)
      (hS j i hw0)) (hw j i)
  · intro hS
    constructor
    · rintro ⟨a, ha0, ha1, heq⟩
      by_cases hB : B = 0
      · have hx0 := CA5_x_of_y x y w hrow hS (CA5_allzero y hy hB)
        exact ⟨0, le_rfl, fun j i _ => by rw [hx0 j, zero_mul]⟩
      by_cases hA : A = 0
      · exact ⟨0, le_rfl, fun j i _ => by rw [CA5_allzero x hx hA j, zero_mul]⟩
      have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
      have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
      have hm := div_pos hAp hBp
      refine ⟨A / B, hm.le, ?_⟩
      intro j0 i0 hw0
      by_contra hne
      have hwp : 0 < w j0 i0 := lt_of_le_of_ne (hw j0 i0) (Ne.symm hw0)
      rcases lt_or_gt_of_ne ha1 with hlt | hgt
      · have : ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) <
            ∑ j, ∑ i, w j i * CA5_L (A / B) a (x j) (y i) := by
          refine Finset.sum_lt_sum (fun j _ => Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (CA5_pt1 _ a _ _ hm ha0.le hlt.le (hx j) (hy i)) (hw j i))
            ⟨j0, Finset.mem_univ _, ?_⟩
          exact Finset.sum_lt_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (CA5_pt1 _ a _ _ hm ha0.le hlt.le (hx j0) (hy i)) (hw j0 i))
            ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left
              (CA5_pt1s _ a _ _ hm ha0 hlt (hx j0) (hy i0) hne) hwp⟩
        rw [hEq a hAp hBp] at this
        linarith
      · have : ∑ j, ∑ i, w j i * CA5_L (A / B) a (x j) (y i) <
            ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) := by
          have hle : ∀ j i, w j i * CA5_L (A / B) a (x j) (y i) ≤
              w j i * (CA5_phi a (x j) * CA5_phi (1 - a) (y i)) := by
            intro j i
            by_cases hw1 : w j i = 0
            · simp [hw1]
            exact mul_le_mul_of_nonneg_left (CA5_pt2 _ a _ _ hm hgt.le (hx j) (hy i)
              (hS j i hw1)) (hw j i)
          refine Finset.sum_lt_sum (fun j _ => Finset.sum_le_sum fun i _ => hle j i)
            ⟨j0, Finset.mem_univ _, ?_⟩
          exact Finset.sum_lt_sum (fun i _ => hle j0 i)
            ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left
              (CA5_pt2s _ a _ _ hm hgt (hx j0) (hy i0) (hS j0 i0 hw0) hne) hwp⟩
        rw [hEq a hAp hBp] at this
        linarith
    · rintro ⟨c, hc, h⟩
      refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      have hpair : ∀ j i, w j i * x j = w j i * (c * y i) := by
        intro j i
        by_cases hw0 : w j i = 0
        · simp [hw0]
        · rw [h j i hw0]
      have hAc : A = c * B := by
        rw [hAdef, hBdef, Finset.mul_sum]
        calc ∑ j, x j = ∑ j, ∑ i, w j i * x j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← Finset.sum_mul, hrow j, one_mul]
          _ = ∑ j, ∑ i, w j i * (c * y i) := by
              simp only [hpair]
          _ = ∑ i, c * y i := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_mul, hcol i, one_mul]
      have hpt : ∀ j i, w j i * (CA5_phi (1 / 2) (x j) * CA5_phi (1 - 1 / 2) (y i)) =
          w j i * (c ^ (1 / 2 : ℝ) * y i) := by
        intro j i
        by_cases hw0 : w j i = 0
        · simp [hw0]
        rw [h j i hw0, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
        congr 1
        by_cases hcy : c * y i = 0
        · rw [hcy, CA5_phi_zero, zero_mul]
          rcases mul_eq_zero.1 hcy with h0 | h0
          · rw [h0, Real.zero_rpow (by norm_num), zero_mul]
          · rw [h0, mul_zero]
        have hy0 : y i ≠ 0 := fun h0 => hcy (by rw [h0, mul_zero])
        have hc0 : c ≠ 0 := fun h0 => hcy (by rw [h0, zero_mul])
        rw [CA5_phi_pos _ _ hcy, CA5_phi_pos _ _ hy0, Real.mul_rpow hc (hy i), mul_assoc,
          ← Real.rpow_add' (hy i) (by norm_num)]
        norm_num
      simp only [hpt]
      rw [hAc, Real.mul_rpow hc hB0, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, mul_assoc,
        ← Real.rpow_add' hB0 (by norm_num), show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
        Real.rpow_one, hBdef, Finset.mul_sum]
      calc ∑ j, ∑ i, w j i * (c ^ (1 / 2 : ℝ) * y i) = ∑ i, ∑ j, w j i * (c ^ (1 / 2 : ℝ) * y i) :=
            Finset.sum_comm
        _ = ∑ i, c ^ (1 / 2 : ℝ) * y i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_mul, hcol i, one_mul]

lemma CA5_cfc_eq {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : cfc f A = (hA.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun j => ((f (hA.eigenvalues j) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix I I ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

lemma CA5_spec {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun j => ((hA.eigenvalues j : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix I I ℂ) := by
  have := CA5_cfc_eq hA id
  rw [cfc_id ℝ A] at this
  simpa using this

lemma CA5_trace_expand {I : Type} [Fintype I] [DecidableEq I] (p l : I → ℝ) (W : Matrix I I ℂ) :
    (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * W * Matrix.diagonal (fun j => ((l j : ℝ) : ℂ))
      * star W).trace.re = ∑ i, l i * ∑ j, Complex.normSq (W j i) * p j := by
  have hM : Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * W *
      Matrix.diagonal (fun j => ((l j : ℝ) : ℂ)) = Matrix.of fun j i => (p j : ℂ) * W j i * l i := by
    ext j i; simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hM]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.star_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ((p j : ℂ) * W j i * (l i : ℂ) * star (W j i)) =
      ((l i * (Complex.normSq (W j i) * p j) : ℝ) : ℂ) := by
    rw [Complex.star_def]
    push_cast
    rw [← Complex.mul_conj]; ring
  rw [this, Complex.ofReal_re]

lemma CA5_normSq_row {I : Type} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ)
    (h : star W * W = 1) (i : I) : ∑ j, Complex.normSq (W j i) = 1 := by
  have := congrArg (fun M => (M i i).re) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.re_sum,
    Complex.one_re] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma CA5_normSq_col {I : Type} [Fintype I] [DecidableEq I] (W : Matrix I I ℂ)
    (h : W * star W = 1) (j : I) : ∑ i, Complex.normSq (W j i) = 1 := by
  have := congrArg (fun M => (M j j).re) h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.re_sum,
    Complex.one_re] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]


lemma CA5_matrix {I : Type} [Fintype I] [DecidableEq I] (X Y : Matrix I I ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∃ x y : I → ℝ, ∃ w : I → I → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, 0 ≤ y i) ∧ (∀ j i, 0 ≤ w j i) ∧
      (∀ j, ∑ i, w j i = 1) ∧ (∀ i, ∑ j, w j i = 1) ∧
      (∀ a b : ℝ, (supportPower X a * supportPower Y b).trace.re =
        ∑ j, ∑ i, w j i * (CA5_phi a (x j) * CA5_phi b (y i))) ∧
      X.trace.re = ∑ j, x j ∧ Y.trace.re = ∑ i, y i ∧
      ((∀ v : I → ℂ, Y.mulVec v = 0 → X.mulVec v = 0) →
        ∀ j i, w j i ≠ 0 → x j ≠ 0 → y i ≠ 0) ∧
      ((∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • Y) ↔ ∃ c : ℝ, 0 ≤ c ∧ ∀ j i, w j i ≠ 0 → x j = c * y i) := by
  have hXh : X.IsHermitian := hX.1
  have hYh : Y.IsHermitian := hY.1
  set U : Matrix I I ℂ := (hXh.eigenvectorUnitary : Matrix I I ℂ) with hUdef
  set V : Matrix I I ℂ := (hYh.eigenvectorUnitary : Matrix I I ℂ) with hVdef
  set x := hXh.eigenvalues with hxdef
  set y := hYh.eigenvalues with hydef
  have hU1 : star U * U = 1 := Unitary.star_mul_self_of_mem hXh.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Unitary.mul_star_self_of_mem hXh.eigenvectorUnitary.2
  have hV1 : star V * V = 1 := Unitary.star_mul_self_of_mem hYh.eigenvectorUnitary.2
  have hV2 : V * star V = 1 := Unitary.mul_star_self_of_mem hYh.eigenvectorUnitary.2
  have hUU : ∀ M : Matrix I I ℂ, U * (star U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hU2, Matrix.one_mul]
  have hUU' : ∀ M : Matrix I I ℂ, star U * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hVV : ∀ M : Matrix I I ℂ, V * (star V * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hV2, Matrix.one_mul]
  have hVV' : ∀ M : Matrix I I ℂ, star V * (V * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hV1, Matrix.one_mul]
  set Dx := Matrix.diagonal (fun j => ((x j : ℝ) : ℂ)) with hDx
  set Dy := Matrix.diagonal (fun j => ((y j : ℝ) : ℂ)) with hDy
  have hXs : X = U * Dx * star U := CA5_spec hXh
  have hYs : Y = V * Dy * star V := CA5_spec hYh
  set W := star U * V with hW
  have hWW1 : star W * W = 1 := by
    rw [hW, StarMul.star_mul, star_star]
    simp only [Matrix.mul_assoc, hUU, hV1]
  have hWW2 : W * star W = 1 := by
    rw [hW, StarMul.star_mul, star_star]
    simp only [Matrix.mul_assoc, hVV, hU1]
  have e1 : star U * X * V = Dx * W := by
    rw [hXs, hW]; simp only [Matrix.mul_assoc, hUU']
  have e2 : star U * Y * V = W * Dy := by
    rw [hYs, hW]; simp only [Matrix.mul_assoc]; rw [hV1, Matrix.mul_one]
  have r1 : U * (Dx * W) * star V = X := by
    rw [hXs, hW]; simp only [Matrix.mul_assoc, hV2, Matrix.mul_one]
  have r2 : U * (W * Dy) * star V = Y := by
    rw [hYs, hW]; simp only [Matrix.mul_assoc, hUU]
  refine ⟨x, y, fun j i => Complex.normSq (W j i), hX.eigenvalues_nonneg, hY.eigenvalues_nonneg,
    fun j i => Complex.normSq_nonneg _, CA5_normSq_col W hWW2, CA5_normSq_row W hWW1, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro a b
    rw [CA5_sp, CA5_sp, CA5_cfc_eq hXh, CA5_cfc_eq hYh]
    have : (U * Matrix.diagonal (fun j => ((CA5_phi a (x j) : ℝ) : ℂ)) * star U *
        (V * Matrix.diagonal (fun j => ((CA5_phi b (y j) : ℝ) : ℂ)) * star V)).trace =
        (Matrix.diagonal (fun j => ((CA5_phi a (x j) : ℝ) : ℂ)) * W *
          Matrix.diagonal (fun j => ((CA5_phi b (y j) : ℝ) : ℂ)) * star W).trace := by
      rw [show U * Matrix.diagonal (fun j => ((CA5_phi a (x j) : ℝ) : ℂ)) * star U *
        (V * Matrix.diagonal (fun j => ((CA5_phi b (y j) : ℝ) : ℂ)) * star V) =
        U * (Matrix.diagonal (fun j => ((CA5_phi a (x j) : ℝ) : ℂ)) * star U * V *
        Matrix.diagonal (fun j => ((CA5_phi b (y j) : ℝ) : ℂ)) * star V) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [hW, StarMul.star_mul, star_star, Matrix.mul_assoc]
    rw [this, CA5_trace_expand, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · rw [hXh.trace_eq_sum_eigenvalues, Complex.re_sum]; simp; rfl
  · rw [hYh.trace_eq_sum_eigenvalues, Complex.re_sum]; simp; rfl
  · intro hS j i hw hx hy
    have hWji : W j i ≠ 0 := fun h => hw (by simp [h])
    have hv : ∀ M : Matrix I I ℂ, M.mulVec (fun k => V k i) = fun k => (M * V) k i := by
      intro M; ext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hYV : Y * V = V * Dy := by
      rw [hYs]; simp only [Matrix.mul_assoc, hV1, Matrix.mul_one]
    have h0 : Y.mulVec (fun k => V k i) = 0 := by
      rw [hv, hYV]; ext k; simp [hDy, Matrix.mul_diagonal, hy]
    have h1 := hS _ h0
    rw [hv] at h1
    have h2 : (star U * (X * V)) j i = 0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => by rw [congrFun h1 k]; simp
    rw [← Matrix.mul_assoc, e1] at h2
    simp [hDx, Matrix.diagonal_mul, hx, hWji] at h2
  · constructor
    · rintro ⟨c, hc, hXY⟩
      refine ⟨c, hc, fun j i hw => ?_⟩
      have hWji : W j i ≠ 0 := fun h => hw (by simp [h])
      have hm : Dx * W = (c : ℂ) • (W * Dy) := by
        rw [← e1, ← e2, hXY, Matrix.mul_smul, Matrix.smul_mul]
      have hji := congrFun (congrFun hm j) i
      simp only [hDx, hDy, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
        smul_eq_mul] at hji
      have h3 : (((x j - c * y i : ℝ)) : ℂ) * W j i = 0 := by
        push_cast; linear_combination hji
      have h4 := (mul_eq_zero.1 h3).resolve_right hWji
      rw [Complex.ofReal_eq_zero, sub_eq_zero] at h4
      exact h4
    · rintro ⟨c, hc, h⟩
      refine ⟨c, hc, ?_⟩
      have hm : Dx * W = (c : ℂ) • (W * Dy) := by
        ext j i
        simp only [hDx, hDy, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
          smul_eq_mul]
        by_cases hWji : W j i = 0
        · simp [hWji]
        · rw [h j i (by simpa [Complex.normSq_eq_zero] using hWji)]
          push_cast; ring
      rw [← r1, ← r2, hm, Matrix.mul_smul, Matrix.smul_mul]

end CA5_helpers

noncomputable section

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Support50.P12 in
/-- Corollary A.5, PDF pp.45–46: both full exponent ranges and the 'some positive
order other than one' equality characterization, including zero operators. -/
theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (X Y : Mat I) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (∀ a ∈ Icc (0 : ℝ) 1, tr (supportPower X a * supportPower Y (1 - a)) ≤
      Real.rpow (tr X) a * Real.rpow (tr Y) (1 - a)) ∧
    (Supports X Y → ∀ a ≥ (1 : ℝ), tr (supportPower X a * supportPower Y (1 - a)) ≥
      Real.rpow (tr X) a * Real.rpow (tr Y) (1 - a)) ∧
    (Supports X Y →
      ((∃ a : ℝ, 0 < a ∧ a ≠ 1 ∧ tr (supportPower X a * supportPower Y (1 - a)) =
        Real.rpow (tr X) a * Real.rpow (tr Y) (1 - a)) ↔
        ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • Y)) := by
  obtain ⟨x, y, w, hx, hy, hw, hrow, hcol, hT, hA, hB, hS, hC⟩ := CA5_matrix X Y hX hY
  obtain ⟨R1, R2, R3⟩ := CA5_real x y w hx hy hw hrow hcol
  have hsup : Supports X Y → ∀ j i, w j i ≠ 0 → x j ≠ 0 → y i ≠ 0 := fun h => hS h
  simp only [tr, Real.rpow_eq_pow, hT, hA, hB, hC]
  refine ⟨fun a ha => R1 a ha.1 ha.2, fun h a ha => R2 (hsup h) a ha, fun h => R3 (hsup h)⟩

end
