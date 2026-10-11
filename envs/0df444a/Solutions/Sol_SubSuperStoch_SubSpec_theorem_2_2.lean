-- Prove2me | solution 1 for SubSuperStoch.SubSpec.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:44:14.33378+00:00
-- url     : https://prove2.me/submissions/cea7bb30-fc7e-4c55-be93-ef594e0b10fe

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace RRAux_SubSuperStoch_SubSpec_theorem_2_2

open Matrix

/-- `v m = F^m 1`, entrywise. -/
def v {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 1
  | m + 1 => fun i => ∑ j, F i j * v F m j

lemma v_zero {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : v F 0 i = 1 := rfl
lemma v_succ {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (i : Fin n) :
    v F (m + 1) i = ∑ j, F i j * v F m j := rfl

lemma eigvec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (h : μ ∈ spectrum ℂ A) :
    ∃ x : Fin n → ℂ, x ≠ 0 ∧ A *ᵥ x = μ • x := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h
  obtain ⟨x, hx, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨x, hx, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at h0
  exact h0.symm

lemma eig_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF0 : ∀ i j, 0 ≤ F i j) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (F.map (algebraMap ℝ ℂ))) (m : ℕ) (β : ℝ)
    (hβ : ∀ i, v F m i ≤ β) : ‖μ‖ ^ m ≤ β := by
  obtain ⟨x, hx, hxe⟩ := eigvec _ μ hμ
  have hrow : ∀ i, μ * x i = ∑ j, (F i j : ℂ) * x j := by
    intro i
    have := congrFun hxe i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply] at this
    exact this.symm
  obtain ⟨j0, hj0⟩ : ∃ j, x j ≠ 0 := by
    by_contra hc; push Not at hc; exact hx (funext hc)
  have : Nonempty (Fin n) := ⟨j0⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => ‖x i‖)
  have hMpos : 0 < ‖x i0‖ := lt_of_lt_of_le (norm_pos_iff.mpr hj0) (hi0 j0)
  have claim : ∀ k i, ‖μ‖ ^ k * ‖x i‖ ≤ ‖x i0‖ * v F k i := by
    intro k
    induction k with
    | zero => intro i; simpa [v_zero] using hi0 i
    | succ k ih =>
      intro i
      calc ‖μ‖ ^ (k + 1) * ‖x i‖ = ‖μ‖ ^ k * ‖μ * x i‖ := by rw [norm_mul]; ring
        _ = ‖μ‖ ^ k * ‖∑ j, (F i j : ℂ) * x j‖ := by rw [hrow]
        _ ≤ ‖μ‖ ^ k * ∑ j, F i j * ‖x j‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF0 i j)]
        _ = ∑ j, F i j * (‖μ‖ ^ k * ‖x j‖) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
        _ ≤ ∑ j, F i j * (‖x i0‖ * v F k j) := by
          exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hF0 i j)
        _ = ‖x i0‖ * v F (k + 1) i := by
          rw [v_succ, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have h1 := claim m i0
  have h2 : ‖x i0‖ * v F m i0 ≤ ‖x i0‖ * β := mul_le_mul_of_nonneg_left (hβ i0) hMpos.le
  nlinarith

section
open SubSuperStoch.SubSpec

variable {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
include hF

lemma v_nonneg : ∀ m i, 0 ≤ v F m i := by
  intro m; induction m with
  | zero => intro i; simp [v_zero]
  | succ m ih => intro i; rw [v_succ]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hF.1 i j) (ih j)

lemma v_le_one : ∀ m i, v F m i ≤ 1 := by
  intro m; induction m with
  | zero => intro i; simp [v_zero]
  | succ m ih =>
    intro i; rw [v_succ]
    calc ∑ j, F i j * v F m j ≤ ∑ j, F i j * 1 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hF.1 i j)
      _ = rowSum F i := by simp [rowSum]
      _ ≤ 1 := hF.2 i

lemma v_succ_le : ∀ m i, v F (m + 1) i ≤ v F m i := by
  intro m; induction m with
  | zero => intro i; rw [v_zero]; exact v_le_one F hF 1 i
  | succ m ih =>
    intro i; rw [v_succ, v_succ F m]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hF.1 i j)

lemma v_anti {m m' : ℕ} (h : m ≤ m') (i : Fin n) : v F m' i ≤ v F m i := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (v_succ_le F hF _ i).trans ih

lemma v_one (i : Fin n) : v F 1 i = rowSum F i := by simp [v_succ, v_zero, rowSum]

lemma chain_step (a b : Fin n) (m : ℕ) (α₂ δ : ℝ) (hα₂ : 0 ≤ α₂) (hδ : 0 ≤ δ)
    (hab : α₂ ≤ F a b) (hb : v F m b ≤ 1 - δ) :
    v F (m + 1) a ≤ 1 - α₂ * δ := by
  rw [v_succ]
  have hs : F a b * (1 - v F m b) ≤ ∑ j, F a j * (1 - v F m j) :=
    Finset.single_le_sum (f := fun j => F a j * (1 - v F m j))
      (fun j _ => mul_nonneg (hF.1 a j) (by linarith [v_le_one F hF m j])) (Finset.mem_univ b)
  have he : ∑ j, F a j * (1 - v F m j) = rowSum F a - ∑ j, F a j * v F m j := by
    simp [rowSum, mul_sub, Finset.sum_sub_distrib]
  have h1 : α₂ * δ ≤ F a b * (1 - v F m b) :=
    mul_le_mul hab (by linarith) hδ (le_trans hα₂ hab)
  linarith [hF.2 a]

end

lemma chain_bound {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : SubSuperStoch.SubSpec.IsSubStochastic F) (c : ℕ → Fin n) (L : ℕ)
    (hc : SubSuperStoch.SubSpec.IsChain F c L) (α₁ α₂ : ℝ) (hα₁ : α₁ ≤ 1) (hα₂ : 0 ≤ α₂)
    (hpos : ∀ i j, 0 < F i j → α₂ ≤ F i j) (h0 : v F 1 (c 0) ≤ α₁) :
    ∀ t, t ≤ L → v F (t + 1) (c t) ≤ 1 - (1 - α₁) * α₂ ^ t := by
  intro t
  induction t with
  | zero => intro _; simp; exact h0
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have hne := (hc t (by omega)).1
    have hgt : 0 < F (c (t + 1)) (c t) := lt_of_le_of_ne (hF.1 _ _) (Ne.symm hne)
    have := chain_step F hF (c (t + 1)) (c t) (t + 1) α₂ ((1 - α₁) * α₂ ^ t) hα₂
      (mul_nonneg (by linarith) (pow_nonneg hα₂ t)) (hpos _ _ hgt) h1
    calc v F (t + 1 + 1) (c (t + 1)) ≤ 1 - α₂ * ((1 - α₁) * α₂ ^ t) := this
      _ = 1 - (1 - α₁) * α₂ ^ (t + 1) := by ring

end RRAux_SubSuperStoch_SubSpec_theorem_2_2

open RRAux_SubSuperStoch_SubSpec_theorem_2_2 in
open SubSuperStoch.SubSpec in
theorem solution {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (hS₁ : ∃ s, rowSum F s < 1) (hS₂ : ∃ s, rowSum F s = 1)
    (len : Fin n → ℕ)
    (hchain : ∀ k, rowSum F k = 1 → ∃ i, rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, rowSum F k = 1 ∧ m = len k} C) :
    (∀ μ ∈ specC F, ‖μ‖ ≤ (1 - (1 - α₁) * α₂ ^ C) ^ (1 / ((C : ℝ) + 1))) ∧
      (1 - (1 - α₁) * α₂ ^ C) ^ (1 / ((C : ℝ) + 1)) < 1 := by
  obtain ⟨⟨s1, hs1, rfl⟩, hα₁g⟩ := hα₁
  obtain ⟨⟨i2, j2, hpos2, rfl⟩, hα₂l⟩ := hα₂
  have hpos : ∀ i j, 0 < F i j → F i2 j2 ≤ F i j := fun i j h => hα₂l ⟨i, j, h, rfl⟩
  have hα₁0 : 0 ≤ rowSum F s1 := Finset.sum_nonneg fun j _ => hF.1 s1 j
  have hα₂1 : F i2 j2 ≤ 1 := by
    have : F i2 j2 ≤ rowSum F i2 :=
      Finset.single_le_sum (f := fun j => F i2 j) (fun j _ => hF.1 i2 j) (Finset.mem_univ j2)
    linarith [hF.2 i2]
  set α₁ := rowSum F s1 with hα₁def
  set α₂ := F i2 j2 with hα₂def
  set b := 1 - (1 - α₁) * α₂ ^ C with hb
  have hpowC : α₂ ^ C ≤ 1 := pow_le_one₀ hpos2.le hα₂1
  have hpowCpos : 0 < α₂ ^ C := pow_pos hpos2 C
  have hbα₁ : α₁ ≤ b := by
    have : (1 - α₁) * α₂ ^ C ≤ (1 - α₁) * 1 := mul_le_mul_of_nonneg_left hpowC (by linarith)
    linarith
  have hb1 : b < 1 := by
    have : 0 < (1 - α₁) * α₂ ^ C := mul_pos (by linarith) hpowCpos
    linarith
  have hb0 : 0 ≤ b := le_trans hα₁0 hbα₁
  -- every row of F^{C+1} 1 is at most b
  have hrows : ∀ k, v F (C + 1) k ≤ b := by
    intro k
    rcases lt_or_eq_of_le (hF.2 k) with hk | hk
    · calc v F (C + 1) k ≤ v F 1 k := v_anti F hF (by omega) k
        _ = rowSum F k := v_one F hF k
        _ ≤ α₁ := hα₁g ⟨k, hk, rfl⟩
        _ ≤ b := hbα₁
    · obtain ⟨i, hi, c, hc0, hcL, _, hcch⟩ := hchain k hk
      have hLC : len k ≤ C := hC.2 ⟨k, hk, rfl⟩
      have h0 : v F 1 (c 0) ≤ α₁ := by
        rw [v_one F hF, hc0]; exact hα₁g ⟨i, hi, rfl⟩
      have hcb := chain_bound F hF c (len k) hcch α₁ α₂ (by linarith) hpos2.le hpos h0 (len k) le_rfl
      rw [hcL] at hcb
      have hpw : α₂ ^ C ≤ α₂ ^ len k := pow_le_pow_of_le_one hpos2.le hα₂1 hLC
      calc v F (C + 1) k ≤ v F (len k + 1) k := v_anti F hF (by omega) k
        _ ≤ 1 - (1 - α₁) * α₂ ^ len k := hcb
        _ ≤ b := by
          have : (1 - α₁) * α₂ ^ C ≤ (1 - α₁) * α₂ ^ len k :=
            mul_le_mul_of_nonneg_left hpw (by linarith)
          linarith
  have hexp : (0:ℝ) < 1 / ((C : ℝ) + 1) := by positivity
  refine ⟨fun μ hμ => ?_, Real.rpow_lt_one hb0 hb1 hexp⟩
  have hμb : ‖μ‖ ^ (C + 1) ≤ b := eig_bound F hF.1 μ hμ (C + 1) b hrows
  have hroot : (‖μ‖ ^ (C + 1)) ^ (1 / ((C : ℝ) + 1)) = ‖μ‖ := by
    have := Real.pow_rpow_inv_natCast (norm_nonneg μ) (Nat.succ_ne_zero C)
    simpa [one_div] using this
  rw [← hroot]
  exact Real.rpow_le_rpow (by positivity) hμb hexp.le

#print axioms solution
