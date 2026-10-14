-- Prove2me | solution 1 for PALM.ProxNMF.eq_4_1_eq_4_2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:09:17.411605+00:00
-- url     : https://prove2.me/submissions/18fedb08-163c-4714-85cf-60750eaf302c

import Mathlib
import Definitions.Def_PALM_ProxNMF_Setting

open CaiCandesShen.ProximalLimit PALM.ProxNMF

namespace TwentyAnalysis.PALM

variable {m n : ℕ}

lemma frob_sum (X : Matrix (Fin m) (Fin n) ℝ) :
    frobInner X X = ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 := by
  simp [frobInner, Fintype.sum_prod_type, pow_two]

lemma facts (U X : Matrix (Fin m) (Fin n) ℝ) :
    frobInner X X = normSqPlus U X + normSqMinus U X ∧
    normSqPlus U (X - U) + normSqMinus U X = frobInner (X - Pplus U) (X - Pplus U) ∧
    (normSqMinus U X = 0 ↔ ∀ p ∈ Iminus U, X p.1 p.2 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [frob_sum]
    simp only [normSqPlus, normSqMinus, Iplus, Iminus, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : 0 ≤ U p.1 p.2
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  · rw [frob_sum]
    simp only [normSqPlus, normSqMinus, Iplus, Iminus, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : 0 ≤ U p.1 p.2
    · simp [h, not_lt.mpr h, Pplus, max_eq_right h, Matrix.sub_apply]
    · simp [h, lt_of_not_ge h, Pplus, max_eq_left (le_of_not_ge h), Matrix.sub_apply]
  · unfold normSqMinus
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun p hp => sq_nonneg (X p.1 p.2))]
    simp only [sq_eq_zero_iff]

noncomputable def mask (U X : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if 0 ≤ U i j then max 0 (X i j) else 0

def good (U X : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ X ∈ NonnegSet m n

lemma mask_good (U X : Matrix (Fin m) (Fin n) ℝ) : good U (mask U X) := by
  constructor
  · intro p hp
    have hu : U p.1 p.2 < 0 := (Finset.mem_filter.mp hp).2
    simp [mask, not_le.mpr hu]
  · intro i j
    unfold mask
    split_ifs <;> positivity

lemma mask_l0 (U X : Matrix (Fin m) (Fin n) ℝ) : l0 (mask U X) ≤ l0 X := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  contrapose! hp
  simp [mask, hp]

lemma mask_fixed (U X : Matrix (Fin m) (Fin n) ℝ) (hX : good U X) : mask U X = X := by
  ext i j
  by_cases hu : 0 ≤ U i j
  · simp [mask, hu, max_eq_right (hX.2 i j)]
  · have hz := hX.1 (i,j) (by simp [Iminus, lt_of_not_ge hu])
    simp [mask, hu, hz]

lemma scalar_clip (u x : ℝ) (hu : 0 ≤ u) :
    (max 0 x - u)^2 ≤ (x - u)^2 ∧
      ((max 0 x - u)^2 = (x - u)^2 → 0 ≤ x) := by
  by_cases hx : 0 ≤ x
  · simp [max_eq_right hx, hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [max_eq_left hx'.le]
    constructor
    · nlinarith [sq_nonneg x]
    · intro he
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hx'.le hu, sq_pos_of_neg hx']

lemma scalar_mask (u x : ℝ) :
    ((if 0 ≤ u then max 0 x else 0) - max 0 u)^2 ≤ (x - max 0 u)^2 ∧
      (((if 0 ≤ u then max 0 x else 0) - max 0 u)^2 = (x - max 0 u)^2 →
        (u < 0 → x = 0) ∧ 0 ≤ x) := by
  by_cases hu : 0 ≤ u
  · simp only [if_pos hu, max_eq_right hu]
    exact ⟨(scalar_clip u x hu).1, fun he => ⟨fun h => (not_lt.mpr hu h).elim,
      (scalar_clip u x hu).2 he⟩⟩
  · have hu' : u < 0 := lt_of_not_ge hu
    simp only [if_neg hu, max_eq_left hu'.le, sub_zero, zero_pow (by decide : 2 ≠ 0)]
    refine ⟨sq_nonneg x, ?_⟩
    intro he
    have hx : x = 0 := sq_eq_zero_iff.mp he.symm
    simp [hx]

lemma mask_dist (U X : Matrix (Fin m) (Fin n) ℝ) :
    frobInner (mask U X - Pplus U) (mask U X - Pplus U) ≤ frobInner (X - Pplus U) (X - Pplus U) ∧
      (frobInner (mask U X - Pplus U) (mask U X - Pplus U) = frobInner (X - Pplus U) (X - Pplus U) → good U X) := by
  rw [frob_sum, frob_sum]
  have hle (p : Fin m × Fin n) (hp : p ∈ Finset.univ) :
      (mask U X - Pplus U) p.1 p.2 ^ 2 ≤ (X - Pplus U) p.1 p.2 ^ 2 :=
    (scalar_mask (U p.1 p.2) (X p.1 p.2)).1
  refine ⟨Finset.sum_le_sum hle, ?_⟩
  intro he
  have heach := (Finset.sum_eq_sum_iff_of_le hle).mp he
  constructor
  · intro p hp
    exact ((scalar_mask (U p.1 p.2) (X p.1 p.2)).2 (heach p (Finset.mem_univ p))).1
      (Finset.mem_filter.mp hp).2
  · intro i j
    exact ((scalar_mask (U i j) (X i j)).2 (heach (i,j) (Finset.mem_univ _))).2

lemma argmin_reduce {α : Type*} (F G : α → ℝ) (C D : Set α) (P : α → α) (k : ℝ)
    (hDC : D ⊆ C) (hPD : ∀ X ∈ C, P X ∈ D)
    (hsame : ∀ X ∈ D, F X = G X + k)
    (hred : ∀ X ∈ C, F (P X) ≤ F X)
    (hfix : ∀ X ∈ C, F (P X) = F X → X ∈ D) :
    argminOn F C = argminOn G D := by
  ext X
  constructor
  · rintro ⟨hX, hmin⟩
    have hXD := hfix X hX (le_antisymm (hred X hX) (hmin _ (hDC (hPD X hX))))
    refine ⟨hXD, fun Y hY => ?_⟩
    have h := hmin Y (hDC hY)
    rw [hsame X hXD, hsame Y hY] at h
    linarith
  · rintro ⟨hX, hmin⟩
    refine ⟨hDC hX, fun Y hY => ?_⟩
    have h := hmin (P Y) (hPD Y hY)
    have hr := hred Y hY
    rw [hsame X hX, hsame (P Y) (hPD Y hY)] at *
    linarith

lemma minus_zero (U X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ p ∈ Iminus U, X p.1 p.2 = 0) : normSqMinus U X = 0 :=
  (facts U X).2.2.mpr h

lemma cross_zero (U X : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ p ∈ Iminus U, X p.1 p.2 = 0) :
    ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2 = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  rw [h p hp, zero_mul]

lemma mask_plus (U X : Matrix (Fin m) (Fin n) ℝ) (hX : X ∈ NonnegSet m n) :
    normSqPlus U (mask U X - U) = normSqPlus U (X - U) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hu : 0 ≤ U p.1 p.2 := (Finset.mem_filter.mp hp).2
  simp [Matrix.sub_apply, mask, hu, max_eq_right (hX p.1 p.2)]

lemma cross_nonpos (U X : Matrix (Fin m) (Fin n) ℝ) (hX : X ∈ NonnegSet m n) :
    ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2 ≤ 0 := by
  apply Finset.sum_nonpos
  intro p hp
  exact mul_nonpos_of_nonneg_of_nonpos (hX p.1 p.2) (Finset.mem_filter.mp hp).2.le

lemma eq42 (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    argminOn (fun X => normSqPlus U (X - U) + normSqMinus U X -
      2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2)
      {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} =
    argminOn (fun X => normSqPlus U (X - U))
      {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ X ∈ NonnegSet m n ∧ l0 X ≤ s} := by
  let F := fun X => normSqPlus U (X - U) + normSqMinus U X -
    2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2
  have hm (X : Matrix (Fin m) (Fin n) ℝ) (hX : X ∈ NonnegSet m n) :
      F (mask U X) = normSqPlus U (X-U) := by
    dsimp [F]
    rw [mask_plus U X hX, minus_zero U _ (mask_good U X).1,
      cross_zero U _ (mask_good U X).1]
    ring
  refine argmin_reduce F (fun X => normSqPlus U (X-U)) _ _ (mask U) 0
    (fun X hX => hX.2) (fun X hX => ⟨(mask_good U X).1, (mask_good U X).2,
      (mask_l0 U X).trans hX.2⟩) ?_ ?_ ?_
  · intro X hX
    dsimp [F]
    rw [minus_zero U X hX.1, cross_zero U X hX.1]
    ring
  · intro X hX
    rw [hm X hX.1]
    have hn : 0 ≤ normSqMinus U X := Finset.sum_nonneg (fun p hp => sq_nonneg _)
    have hc := cross_nonpos U X hX.1
    dsimp [F]
    linarith
  · intro X hX he
    rw [hm X hX.1] at he
    have hn : 0 ≤ normSqMinus U X := Finset.sum_nonneg (fun p hp => sq_nonneg _)
    have hc := cross_nonpos U X hX.1
    have hz : normSqMinus U X = 0 := by dsimp [F] at he; linarith
    exact ⟨(facts U X).2.2.mp hz, hX⟩

lemma remove_nonneg (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    argminOn (fun X => normSqPlus U (X - U))
      {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ X ∈ NonnegSet m n ∧ l0 X ≤ s} =
    argminOn (fun X => normSqPlus U (X - U))
      {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ l0 X ≤ s} := by
  symm
  have he (X : Matrix (Fin m) (Fin n) ℝ) (hz : ∀ p ∈ Iminus U, X p.1 p.2 = 0) :
      frobInner (X-Pplus U) (X-Pplus U) = normSqPlus U (X-U) := by
    rw [← (facts U X).2.1, minus_zero U X hz, add_zero]
  refine argmin_reduce (fun X => normSqPlus U (X-U)) (fun X => normSqPlus U (X-U))
    _ _ (mask U) 0 (fun X hX => ⟨hX.1, hX.2.2⟩)
    (fun X hX => ⟨(mask_good U X).1, (mask_good U X).2, (mask_l0 U X).trans hX.2⟩)
    (fun X hX => by ring) ?_ ?_
  · intro X hX
    have h := (mask_dist U X).1
    rw [he X hX.1, he (mask U X) (mask_good U X).1] at h
    exact h
  · intro X hX hx
    have hh : frobInner (mask U X-Pplus U) (mask U X-Pplus U) =
        frobInner (X-Pplus U) (X-Pplus U) := by
      rw [he X hX.1, he (mask U X) (mask_good U X).1]
      exact hx
    exact ⟨hX.1, ((mask_dist U X).2 hh).2, hX.2⟩

lemma diff_comm (U X : Matrix (Fin m) (Fin n) ℝ) :
    frobInner (U-X) (U-X) = frobInner (X-U) (X-U) := by
  rw [frob_sum, frob_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Matrix.sub_apply]
  ring

lemma ts_eq (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    Ts s (Pplus U) = argminOn (fun X => normSqPlus U (X-U))
      {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ l0 X ≤ s} := by
  unfold Ts
  simp only [diff_comm]
  refine argmin_reduce (fun X => frobInner (X-Pplus U) (X-Pplus U))
    (fun X => normSqPlus U (X-U)) (SparseSet m n s) _ (mask U) 0
    (fun X hX => hX.2)
    (fun X hX => ⟨(mask_good U X).1, (mask_l0 U X).trans hX⟩) ?_
    (fun X hX => (mask_dist U X).1) (fun X hX he => ⟨((mask_dist U X).2 he).1, hX⟩)
  intro X hX
  rw [← (facts U X).2.1, minus_zero U X hX.1]

lemma decomposition (U X : Matrix (Fin m) (Fin n) ℝ) :
    frobInner (X-U) (X-U) = normSqPlus U (X-U) + normSqMinus U X -
      2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2 + normSqMinus U U := by
  have hneg : normSqMinus U (X-U) = normSqMinus U X -
      2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2 + normSqMinus U U := by
    unfold normSqMinus
    calc
      _ = ∑ p ∈ Iminus U, (X p.1 p.2 ^ 2 - 2 * (X p.1 p.2 * U p.1 p.2) + U p.1 p.2 ^ 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Matrix.sub_apply]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [(facts U (X-U)).1, hneg]
  ring

lemma argmin_affine {α : Type*} (F G : α → ℝ) (C : Set α) (a b : ℝ) (ha : 0 < a)
    (he : ∀ X, F X = a * G X + b) : argminOn F C = argminOn G C := by
  ext X
  simp only [argminOn, Set.mem_setOf_eq, he, add_le_add_iff_right,
    mul_le_mul_iff_right₀ ha]

lemma main_real (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    argminOn (fun X => 1/2 * frobInner (X-U) (X-U))
      {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} = Ts s (Pplus U) := by
  rw [argmin_affine _ (fun X => normSqPlus U (X-U) + normSqMinus U X -
    2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2) _ (1/2) (1/2 * normSqMinus U U) (by norm_num)
    (fun X => by rw [decomposition U X]; ring)]
  rw [eq42, remove_nonneg, ts_eq]

lemma f_good (s : ℕ) (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : X ∈ NonnegSet m n ∧ l0 X ≤ s) : f s X = 0 := by
  simp [f, indicator, hX.1, show X ∈ SparseSet m n s from hX.2]

lemma f_bad (s : ℕ) (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : ¬(X ∈ NonnegSet m n ∧ l0 X ≤ s)) : f s X = ⊤ := by
  classical
  by_cases hN : X ∈ NonnegSet m n
  · have hS : X ∉ SparseSet m n s := fun h => hX ⟨hN, h⟩
    simp [f, indicator, hN, hS]
  · by_cases hS : X ∈ SparseSet m n s <;> simp [f, indicator, hN, hS]

lemma prox_eq (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    proxSet (f s) 1 U = argminOn (fun X => 1/2 * frobInner (X-U) (X-U))
      {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} := by
  have hzero : (0 : Matrix (Fin m) (Fin n) ℝ) ∈ NonnegSet m n ∧ l0 (0 : Matrix (Fin m) (Fin n) ℝ) ≤ s := by
    simp [NonnegSet, l0]
  ext X
  constructor
  · intro hX
    have hXC : X ∈ NonnegSet m n ∧ l0 X ≤ s := by
      by_contra h
      have h0 := hX 0
      rw [f_bad s X h, f_good s 0 hzero] at h0
      rw [EReal.top_add_coe, zero_add] at h0
      exact EReal.coe_ne_top _ (top_le_iff.mp h0)
    refine ⟨hXC, fun W hW => ?_⟩
    have h := hX W
    rw [f_good s X hXC, f_good s W hW, zero_add, zero_add] at h
    exact EReal.coe_le_coe_iff.mp h
  · rintro ⟨hXC, hX⟩ W
    by_cases hW : W ∈ NonnegSet m n ∧ l0 W ≤ s
    · rw [f_good s X hXC, f_good s W hW, zero_add, zero_add]
      exact EReal.coe_le_coe_iff.mpr (hX W hW)
    · rw [f_bad s W hW]
      rw [EReal.top_add_coe]
      exact le_top

end TwentyAnalysis.PALM

theorem solution {m n : ℕ} (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) :
    argminOn
        (fun X => normSqPlus U (X - U) + normSqMinus U X
          - 2 * ∑ p ∈ Iminus U, X p.1 p.2 * U p.1 p.2)
        {X | X ∈ NonnegSet m n ∧ l0 X ≤ s} =
      argminOn (fun X => normSqPlus U (X - U))
        {X | (∀ p ∈ Iminus U, X p.1 p.2 = 0) ∧ X ∈ NonnegSet m n ∧ l0 X ≤ s} := by
  exact TwentyAnalysis.PALM.eq42 s U
