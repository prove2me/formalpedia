-- Prove2me | solution 1 for SubSuperStoch.SuperSpec.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:49:12.247981+00:00
-- url     : https://prove2.me/submissions/7490852d-0b19-47fd-b739-3b4d65b7e6d3

import Mathlib
import Definitions.Def_SubSuperStoch_SuperSpec_Setting

namespace RRAux_SubSuperStoch_SuperSpec_theorem_2_6

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

variable {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF0 : ∀ i j, 0 ≤ F i j)
include hF0

lemma v_nonneg : ∀ m i, 0 ≤ v F m i := by
  intro m; induction m with
  | zero => intro i; simp [v_zero]
  | succ m ih => intro i; rw [v_succ]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hF0 i j) (ih j)

lemma v_succ_le_of (m : ℕ) (U : ℝ) (hU : ∀ j, v F m j ≤ U) (a : Fin n) :
    v F (m + 1) a ≤ U * rowSum F a := by
  rw [v_succ]
  calc ∑ j, F a j * v F m j ≤ ∑ j, F a j * U :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hU j) (hF0 a j)
    _ = U * rowSum F a := by simp [rowSum, Finset.mul_sum, mul_comm]

lemma v_le_pow (α₃ : ℝ) (hα₃ : 0 ≤ α₃) (hrow : ∀ i, rowSum F i ≤ α₃) :
    ∀ m i, v F m i ≤ α₃ ^ m := by
  intro m; induction m with
  | zero => intro i; simp [v_zero]
  | succ m ih =>
    intro i
    calc v F (m + 1) i ≤ α₃ ^ m * rowSum F i := v_succ_le_of F hF0 m _ ih i
      _ ≤ α₃ ^ m * α₃ := mul_le_mul_of_nonneg_left (hrow i) (pow_nonneg hα₃ m)
      _ = α₃ ^ (m + 1) := by ring

lemma chain_step (a b : Fin n) (m : ℕ) (U α₂ α₃ δ : ℝ) (hα₂ : 0 ≤ α₂) (hδ : 0 ≤ δ)
    (hU0 : 0 ≤ U) (hrow : rowSum F a ≤ α₃)
    (hU : ∀ j, v F m j ≤ U) (hab : α₂ ≤ F a b) (hb : v F m b ≤ U - δ) :
    v F (m + 1) a ≤ U * α₃ - α₂ * δ := by
  rw [v_succ]
  have hs : F a b * (U - v F m b) ≤ ∑ j, F a j * (U - v F m j) :=
    Finset.single_le_sum (f := fun j => F a j * (U - v F m j))
      (fun j _ => mul_nonneg (hF0 a j) (by linarith [hU j])) (Finset.mem_univ b)
  have he : ∑ j, F a j * (U - v F m j) = U * rowSum F a - ∑ j, F a j * v F m j := by
    simp [rowSum, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]
  have h1 : α₂ * δ ≤ F a b * (U - v F m b) :=
    mul_le_mul hab (by linarith) hδ (le_trans hα₂ hab)
  have h2 : U * rowSum F a ≤ U * α₃ := mul_le_mul_of_nonneg_left hrow hU0
  linarith

lemma chain_bound (c : ℕ → Fin n) (L : ℕ) (hc : IsChain F c L) (α₁ α₂ α₃ : ℝ)
    (hα₁₃ : α₁ ≤ α₃) (hα₂ : 0 ≤ α₂) (hα₃ : 0 ≤ α₃) (hrow : ∀ i, rowSum F i ≤ α₃)
    (hpos : ∀ i j, 0 < F i j → α₂ ≤ F i j) (h0 : rowSum F (c 0) ≤ α₁) (p : ℕ) :
    ∀ t, t ≤ L → v F (p + t + 1) (c t) ≤ α₃ ^ p * (α₃ ^ (t + 1) - (α₃ - α₁) * α₂ ^ t) := by
  intro t
  induction t with
  | zero =>
    intro _
    have := v_succ_le_of F hF0 p _ (v_le_pow F hF0 α₃ hα₃ hrow p) (c 0)
    calc v F (p + 0 + 1) (c 0) ≤ α₃ ^ p * rowSum F (c 0) := by simpa using this
      _ ≤ α₃ ^ p * α₁ := mul_le_mul_of_nonneg_left h0 (pow_nonneg hα₃ p)
      _ = α₃ ^ p * (α₃ ^ (0 + 1) - (α₃ - α₁) * α₂ ^ 0) := by ring
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have hne := (hc t (by omega)).1
    have hgt : 0 < F (c (t + 1)) (c t) := lt_of_le_of_ne (hF0 _ _) (Ne.symm hne)
    have hδ : 0 ≤ α₃ ^ p * ((α₃ - α₁) * α₂ ^ t) :=
      mul_nonneg (pow_nonneg hα₃ p) (mul_nonneg (by linarith) (pow_nonneg hα₂ t))
    have := chain_step F hF0 (c (t + 1)) (c t) (p + t + 1) (α₃ ^ (p + t + 1)) α₂ α₃
      (α₃ ^ p * ((α₃ - α₁) * α₂ ^ t)) hα₂ hδ (pow_nonneg hα₃ _) (hrow _)
      (v_le_pow F hF0 α₃ hα₃ hrow _) (hpos _ _ hgt)
      (by
        calc v F (p + t + 1) (c t) ≤ α₃ ^ p * (α₃ ^ (t + 1) - (α₃ - α₁) * α₂ ^ t) := h1
          _ = α₃ ^ (p + t + 1) - α₃ ^ p * ((α₃ - α₁) * α₂ ^ t) := by ring)
    calc v F (p + (t + 1) + 1) (c (t + 1)) = v F (p + t + 1 + 1) (c (t + 1)) := by
          congr 1
      _ ≤ α₃ ^ (p + t + 1) * α₃ - α₂ * (α₃ ^ p * ((α₃ - α₁) * α₂ ^ t)) := this
      _ = α₃ ^ p * (α₃ ^ (t + 1 + 1) - (α₃ - α₁) * α₂ ^ (t + 1)) := by ring

end

lemma beta_lt_one (β : ℝ) (C : ℕ) (hC : 1 ≤ C) (h : β ^ (1 / (C : ℝ)) < 1) : β < 1 := by
  by_contra hb
  push Not at hb
  have : 1 ≤ β ^ (1 / (C : ℝ)) := Real.one_le_rpow hb (by positivity)
  linarith

end RRAux_SubSuperStoch_SuperSpec_theorem_2_6

open RRAux_SubSuperStoch_SuperSpec_theorem_2_6 in
open SubSuperStoch.SuperSpec in
theorem solution {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSuperStochastic F)
    (hR₁ : ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1) (hR₂ : ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s)
    (len : Fin n → ℕ)
    (hchain : ∀ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k → ∃ i, SubSuperStoch.SubSpec.rowSum F i < 1 ∧
      ∃ c : ℕ → Fin n, c 0 = i ∧ c (len k) = k ∧ 1 ≤ len k ∧ SubSuperStoch.SubSpec.IsChain F c (len k))
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, SubSuperStoch.SubSpec.rowSum F s < 1 ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (α₃ : ℝ) (hα₃ : IsGreatest {x | ∃ s, 1 ≤ SubSuperStoch.SubSpec.rowSum F s ∧ x = SubSuperStoch.SubSpec.rowSum F s} α₃)
    (C : ℕ) (hC : IsGreatest {m | ∃ k, 1 ≤ SubSuperStoch.SubSpec.rowSum F k ∧ m = len k} C)
    (h25 : (α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C) ^ (1 / (C : ℝ)) < 1) :
    ∀ μ ∈ SubSuperStoch.SubSpec.specC F, ‖μ‖ < 1 := by
  have hF0 := hF.1
  obtain ⟨⟨s1, hs1, rfl⟩, hα₁g⟩ := hα₁
  obtain ⟨⟨i2, j2, hpos2, rfl⟩, hα₂l⟩ := hα₂
  obtain ⟨⟨s3, hs3, rfl⟩, hα₃g⟩ := hα₃
  have hpos : ∀ i j, 0 < F i j → F i2 j2 ≤ F i j := fun i j h => hα₂l ⟨i, j, h, rfl⟩
  have hα₁0 : 0 ≤ SubSuperStoch.SubSpec.rowSum F s1 := Finset.sum_nonneg fun j _ => hF0 s1 j
  have hrow : ∀ i, SubSuperStoch.SubSpec.rowSum F i ≤ SubSuperStoch.SubSpec.rowSum F s3 := by
    intro i
    rcases lt_or_ge (SubSuperStoch.SubSpec.rowSum F i) 1 with h | h
    · linarith
    · exact hα₃g ⟨i, h, rfl⟩
  have hα₂₃ : F i2 j2 ≤ SubSuperStoch.SubSpec.rowSum F s3 := by
    have : F i2 j2 ≤ SubSuperStoch.SubSpec.rowSum F i2 :=
      Finset.single_le_sum (f := fun j => F i2 j) (fun j _ => hF0 i2 j) (Finset.mem_univ j2)
    linarith [hrow i2]
  set α₁ := SubSuperStoch.SubSpec.rowSum F s1 with hα₁def
  set α₂ := F i2 j2 with hα₂def
  set α₃ := SubSuperStoch.SubSpec.rowSum F s3 with hα₃def
  set β := α₃ ^ (C + 1) - (α₃ - α₁) * α₂ ^ C with hβ
  have hα₃0 : 0 ≤ α₃ := by linarith
  have hC1 : 1 ≤ C := by
    obtain ⟨k, hk⟩ := hR₂
    obtain ⟨_, _, c, _, _, hl, _⟩ := hchain k hk
    exact le_trans hl (hC.2 ⟨k, hk, rfl⟩)
  have hβ1 : β < 1 := beta_lt_one β C hC1 h25
  have hpowle : α₂ ^ C ≤ α₃ ^ C := pow_le_pow_left₀ hpos2.le hα₂₃ C
  have hrows : ∀ k, v F (C + 1) k ≤ β := by
    intro k
    rcases lt_or_ge (SubSuperStoch.SubSpec.rowSum F k) 1 with hk | hk
    · have h1 := v_succ_le_of F hF0 C _ (v_le_pow F hF0 α₃ hα₃0 hrow C) k
      have h2 : SubSuperStoch.SubSpec.rowSum F k ≤ α₁ := hα₁g ⟨k, hk, rfl⟩
      have h3 : α₃ ^ C * SubSuperStoch.SubSpec.rowSum F k ≤ α₃ ^ C * α₁ :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hα₃0 C)
      have h4 : (α₃ - α₁) * α₂ ^ C ≤ (α₃ - α₁) * α₃ ^ C :=
        mul_le_mul_of_nonneg_left hpowle (by linarith)
      have h5 : β = α₃ ^ C * α₃ - (α₃ - α₁) * α₂ ^ C := by rw [hβ]; ring
      nlinarith
    · obtain ⟨i, hi, c, hc0, hcL, _, hcch⟩ := hchain k hk
      have hLC : len k ≤ C := hC.2 ⟨k, hk, rfl⟩
      have h0 : SubSuperStoch.SubSpec.rowSum F (c 0) ≤ α₁ := by
        rw [hc0]; exact hα₁g ⟨i, hi, rfl⟩
      have hcb := chain_bound F hF0 c (len k) hcch α₁ α₂ α₃ (by linarith) hpos2.le hα₃0 hrow hpos h0
        (C - len k) (len k) le_rfl
      rw [hcL, show C - len k + len k + 1 = C + 1 by omega] at hcb
      have hp1 : α₃ ^ (C - len k) * α₃ ^ (len k + 1) = α₃ ^ (C + 1) := by
        rw [← pow_add]; congr 1; omega
      have hp2 : α₂ ^ C ≤ α₃ ^ (C - len k) * α₂ ^ len k := by
        calc α₂ ^ C = α₂ ^ (C - len k) * α₂ ^ len k := by rw [← pow_add]; congr 1; omega
          _ ≤ α₃ ^ (C - len k) * α₂ ^ len k :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpos2.le hα₂₃ _) (pow_nonneg hpos2.le _)
      have h4 : (α₃ - α₁) * α₂ ^ C ≤ (α₃ - α₁) * (α₃ ^ (C - len k) * α₂ ^ len k) :=
        mul_le_mul_of_nonneg_left hp2 (by linarith)
      calc v F (C + 1) k ≤ α₃ ^ (C - len k) * (α₃ ^ (len k + 1) - (α₃ - α₁) * α₂ ^ len k) := hcb
        _ = α₃ ^ (C + 1) - (α₃ - α₁) * (α₃ ^ (C - len k) * α₂ ^ len k) := by rw [← hp1]; ring
        _ ≤ β := by rw [hβ]; linarith
  intro μ hμ
  have hμb : ‖μ‖ ^ (C + 1) ≤ β := eig_bound F hF0 μ hμ (C + 1) β hrows
  by_contra hcon
  push Not at hcon
  have : 1 ≤ ‖μ‖ ^ (C + 1) := one_le_pow₀ hcon
  linarith

#print axioms solution
