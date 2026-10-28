-- Prove2me | solution 1 for ShadowTomography.ClassicalLB.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:11:55.60703+00:00
-- url     : https://prove2.me/submissions/06c5a4c6-38cb-49d7-b8ab-1e924ae17378

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_ClassicalLB_IsEffect
import Definitions.Def_ShadowTomography_ClassicalLB_tensorPow
import Definitions.Def_ShadowTomography_ClassicalLB_POVM

set_option autoImplicit false

open scoped ComplexOrder

namespace ShadowTomography.ClassicalLB

lemma lb16_tp_diag {Y : Type} [Fintype Y] [DecidableEq Y] (f : Y → ℝ) (k : ℕ) :
    tensorPow (Matrix.diagonal (fun y => ((f y : ℝ) : ℂ))) k
      = Matrix.diagonal (fun x : Fin k → Y => (((∏ t, f (x t)) : ℝ) : ℂ)) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [tensorPow, Matrix.diagonal_apply, Complex.ofReal_prod]
  · obtain ⟨t, ht⟩ : ∃ t, x t ≠ y t := by
      by_contra hc; exact h (funext (fun t => not_not.mp (fun ht => hc ⟨t, ht⟩)))
    simp only [tensorPow, Matrix.diagonal_apply, h, if_false]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])

open Classical in
noncomputable def lb16_W {Y Ω : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (A : Ω → Prop) (x : Fin k → Y) : ℝ :=
  ∑ ω, if A ω then (P.op ω x x).re else 0

lemma lb16_op_re_nonneg {Y Ω : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (ω : Ω) (x : Fin k → Y) : 0 ≤ (P.op ω x x).re := by
  have h := (P.positive ω).diag_nonneg (i := x)
  simpa using (Complex.le_def.mp h).1

lemma lb16_op_re_sum {Y Ω : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (x : Fin k → Y) : ∑ ω, (P.op ω x x).re = 1 := by
  rw [← Complex.re_sum, ← Matrix.sum_apply, P.complete]; simp

lemma lb16_W_nonneg {Y Ω : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (A : Ω → Prop) (x : Fin k → Y) : 0 ≤ lb16_W P A x := by
  unfold lb16_W
  refine Finset.sum_nonneg (fun ω _ => ?_)
  split_ifs
  · exact lb16_op_re_nonneg P ω x
  · exact le_rfl

open Classical in
lemma lb16_W_le_one {Y Ω : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (A : Ω → Prop) (x : Fin k → Y) : lb16_W P A x ≤ 1 := by
  unfold lb16_W
  calc (∑ ω, if A ω then (P.op ω x x).re else 0) ≤ ∑ ω, (P.op ω x x).re :=
        Finset.sum_le_sum (fun ω _ => by
          split_ifs
          · exact le_rfl
          · exact lb16_op_re_nonneg P ω x)
    _ = 1 := lb16_op_re_sum P x

open Classical in
lemma lb16_W_sum_le {Y Ω ι : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] [Fintype ι] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (A : ι → Ω → Prop) (L : ℝ)
    (hL : ∀ ω, ((Finset.univ.filter (fun i => A i ω)).card : ℝ) ≤ L) (x : Fin k → Y) :
    ∑ i, lb16_W P (A i) x ≤ L := by
  unfold lb16_W
  rw [Finset.sum_comm]
  calc ∑ ω, ∑ i, (if A i ω then (P.op ω x x).re else 0)
        = ∑ ω, ((Finset.univ.filter (fun i => A i ω)).card : ℝ) * (P.op ω x x).re := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ ω, L * (P.op ω x x).re :=
          Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_right (hL ω) (lb16_op_re_nonneg P ω x))
    _ = L := by rw [← Finset.mul_sum, lb16_op_re_sum P x, mul_one]

lemma lb16_prob_diag {Y Ω : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (f : Y → ℝ) (A : Ω → Prop) :
    P.prob (tensorPow (Matrix.diagonal (fun y => ((f y : ℝ) : ℂ))) k) A
      = ∑ x : Fin k → Y, (∏ t, f (x t)) * lb16_W P A x := by
  classical
  rw [lb16_tp_diag]
  unfold POVM.prob lb16_W
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Complex.re_sum, Complex.re_mul_ofReal]
  rw [Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  split_ifs
  · refine Finset.sum_congr rfl (fun x _ => ?_); ring
  · simp

open Classical in
lemma lb16_core {Y Ω ι : Type} [Fintype Y] [DecidableEq Y] [Fintype Ω] [Fintype ι] {k : ℕ}
    (P : POVM Ω (Fin k → Y)) (q : Y → ℝ) (hq0 : ∀ y, 0 ≤ q y) (hq1 : ∑ y, q y = 1)
    (r : ι → Y → ℝ) (X L : ℝ) (hX : ∀ i, ∑ y, (r i y) ^ 2 * q y = X) (hX0 : 0 < X)
    (A : ι → Ω → Prop) (hL : ∀ ω, ((Finset.univ.filter (fun i => A i ω)).card : ℝ) ≤ L)
    (hs : ∀ i, (2 / 3 : ℝ) ≤
      P.prob (tensorPow (Matrix.diagonal (fun y => ((r i y * q y : ℝ) : ℂ))) k) (A i)) :
    (4 / 9 : ℝ) * Fintype.card ι ≤ L * X ^ k := by
  set Z := X ^ k with hZ
  have hZ0 : 0 < Z := pow_pos hX0 k
  have hQ1 : ∑ x : Fin k → Y, ∏ t, q (x t) = 1 := by
    rw [← Fintype.sum_pow, hq1, one_pow]
  have hRQ : ∀ i, ∑ x : Fin k → Y, (∏ t, r i (x t)) ^ 2 * ∏ t, q (x t) = Z := by
    intro i; rw [hZ, ← hX i, Fintype.sum_pow]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  set t : ℝ := 2 / (3 * Z) with ht
  have ht0 : 0 < t := by positivity
  have key : ∀ i, 2 * t * (2 / 3) ≤ t ^ 2 * Z + ∑ x : Fin k → Y, (∏ s, q (x s)) * lb16_W P (A i) x := by
    intro i
    have h1 := hs i
    rw [lb16_prob_diag] at h1
    have hpt : ∀ x : Fin k → Y, 2 * t * ((∏ s, (r i (x s) * q (x s))) * lb16_W P (A i) x) ≤
        t ^ 2 * ((∏ s, r i (x s)) ^ 2 * ∏ s, q (x s)) + (∏ s, q (x s)) * lb16_W P (A i) x := by
      intro x
      rw [Finset.prod_mul_distrib]
      have hq : 0 ≤ ∏ s, q (x s) := Finset.prod_nonneg (fun s _ => hq0 _)
      have hw0 := lb16_W_nonneg P (A i) x
      have hw1 := lb16_W_le_one P (A i) x
      nlinarith [mul_nonneg hq (sq_nonneg (t * ∏ s, r i (x s) - lb16_W P (A i) x)),
        mul_nonneg hq (mul_nonneg hw0 (sub_nonneg.2 hw1))]
    calc 2 * t * (2 / 3) ≤ 2 * t * ∑ x : Fin k → Y, (∏ s, (r i (x s) * q (x s))) * lb16_W P (A i) x := by
          gcongr
      _ = ∑ x : Fin k → Y, 2 * t * ((∏ s, (r i (x s) * q (x s))) * lb16_W P (A i) x) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ x : Fin k → Y, (t ^ 2 * ((∏ s, r i (x s)) ^ 2 * ∏ s, q (x s)) +
            (∏ s, q (x s)) * lb16_W P (A i) x) := Finset.sum_le_sum (fun x _ => hpt x)
      _ = t ^ 2 * Z + ∑ x : Fin k → Y, (∏ s, q (x s)) * lb16_W P (A i) x := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hRQ i]
  have hsumY : ∑ i, ∑ x : Fin k → Y, (∏ s, q (x s)) * lb16_W P (A i) x ≤ L := by
    rw [Finset.sum_comm]
    calc ∑ x : Fin k → Y, ∑ i, (∏ s, q (x s)) * lb16_W P (A i) x
          = ∑ x : Fin k → Y, (∏ s, q (x s)) * ∑ i, lb16_W P (A i) x := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ x : Fin k → Y, (∏ s, q (x s)) * L :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (lb16_W_sum_le P A L hL x)
            (Finset.prod_nonneg (fun s _ => hq0 _)))
      _ = L := by rw [← Finset.sum_mul, hQ1, one_mul]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, nsmul_eq_mul] at hsum
  have e1 : 2 * t * (2 / 3) = 2 * (4 / (9 * Z)) := by rw [ht]; field_simp; ring
  have e2 : t ^ 2 * Z = 4 / (9 * Z) := by rw [ht]; field_simp; ring
  rw [e1, e2] at hsum
  have h3 : (Fintype.card ι : ℝ) * (4 / (9 * Z)) ≤ L := by nlinarith
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at h3
  nlinarith

lemma lb16_trace_diag {Y : Type} [Fintype Y] [DecidableEq Y] (c p : Y → ℝ) :
    ((Matrix.diagonal (fun y => ((c y : ℝ) : ℂ))) *
      Matrix.diagonal (fun y => ((p y : ℝ) : ℂ))).trace.re = ∑ y, c y * p y := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma lb16_eff01 {Y : Type} [Fintype Y] [DecidableEq Y] (c : Y → ℝ) (hc : ∀ y, c y = 0 ∨ c y = 1) :
    IsEffect (Matrix.diagonal (fun y => ((c y : ℝ) : ℂ))) ∧
      (Matrix.diagonal (fun y => ((c y : ℝ) : ℂ))).IsDiag ∧
      ∀ x, (Matrix.diagonal (fun y => ((c y : ℝ) : ℂ))) x x = 0 ∨
        (Matrix.diagonal (fun y => ((c y : ℝ) : ℂ))) x x = 1 := by
  refine ⟨⟨?_, ?_⟩, Matrix.isDiag_diagonal _, fun x => ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]; intro y; rcases hc y with h | h <;> simp [h]
  · rw [← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
    intro y; rcases hc y with h | h <;> simp [h]
  · rw [Matrix.diagonal_apply_eq]; rcases hc x with h | h <;> simp [h]

lemma lb16_dens {Y : Type} [Fintype Y] [DecidableEq Y] (p : Y → ℝ) (h0 : ∀ y, 0 ≤ p y)
    (h1 : ∑ y, p y = 1) : WildeQIT.IsDensityOperator (Matrix.diagonal (fun y => ((p y : ℝ) : ℂ))) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]; intro y; exact Complex.zero_le_real.mpr (h0 y)
  · rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, h1]; simp

noncomputable def lb16_qf (n : ℕ) (Z : Type) : (Fin n × Bool) ⊕ Z → ℝ :=
  Sum.elim (fun _ => 1 / (2 * (n : ℝ))) (fun _ => 0)

noncomputable def lb16_rf (n : ℕ) (Z : Type) (a : ℝ) (σ : Fin n → Bool) : (Fin n × Bool) ⊕ Z → ℝ :=
  Sum.elim (fun z => if σ z.1 = z.2 then 1 + a else 1 - a) (fun _ => 0)

noncomputable def lb16_tf (n : ℕ) (Z : Type) (τ : Fin n → Bool) : (Fin n × Bool) ⊕ Z → ℝ :=
  Sum.elim (fun z => if τ z.1 = z.2 then 1 else 0) (fun _ => 0)

lemma lb16_sum_FB {n : ℕ} (F : Fin n × Bool → ℝ) : ∑ z, F z = ∑ j, (F (j, true) + F (j, false)) := by
  rw [Fintype.sum_prod_type]; simp [Fintype.sum_bool]

lemma lb16_sum_qf (n : ℕ) (Z : Type) [Fintype Z] (hn : 0 < n) : ∑ s, lb16_qf n Z s = 1 := by
  rw [Fintype.sum_sum_type, lb16_sum_FB]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp only [lb16_qf, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp; ring

lemma lb16_sum_rq (n : ℕ) (Z : Type) [Fintype Z] (hn : 0 < n) (a : ℝ) (σ : Fin n → Bool) :
    ∑ s, lb16_rf n Z a σ s * lb16_qf n Z s = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ j : Fin n, lb16_rf n Z a σ (Sum.inl (j, true)) * lb16_qf n Z (Sum.inl (j, true)) +
      lb16_rf n Z a σ (Sum.inl (j, false)) * lb16_qf n Z (Sum.inl (j, false)) = 1 / n := by
    intro j
    simp only [lb16_rf, lb16_qf, Sum.elim_inl]
    rcases Bool.eq_false_or_eq_true (σ j) with h | h <;> simp [h] <;> field_simp <;> ring
  rw [Fintype.sum_sum_type, lb16_sum_FB, Finset.sum_congr rfl (fun j _ => h j)]
  simp [lb16_qf]
  field_simp

lemma lb16_sum_r2q (n : ℕ) (Z : Type) [Fintype Z] (hn : 0 < n) (a : ℝ) (σ : Fin n → Bool) :
    ∑ s, (lb16_rf n Z a σ s) ^ 2 * lb16_qf n Z s = 1 + a ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ j : Fin n, (lb16_rf n Z a σ (Sum.inl (j, true))) ^ 2 * lb16_qf n Z (Sum.inl (j, true)) +
      (lb16_rf n Z a σ (Sum.inl (j, false))) ^ 2 * lb16_qf n Z (Sum.inl (j, false)) = (1 + a ^ 2) / n := by
    intro j
    simp only [lb16_rf, lb16_qf, Sum.elim_inl]
    rcases Bool.eq_false_or_eq_true (σ j) with h | h <;> simp [h] <;> field_simp <;> ring
  rw [Fintype.sum_sum_type, lb16_sum_FB, Finset.sum_congr rfl (fun j _ => h j)]
  simp [lb16_qf]
  field_simp

lemma lb16_sum_trq (n : ℕ) (Z : Type) [Fintype Z] (hn : 0 < n) (a : ℝ) (τ σ : Fin n → Bool) :
    ∑ s, lb16_tf n Z τ s * (lb16_rf n Z a σ s * lb16_qf n Z s)
      = ((n : ℝ) * (1 + a) - 2 * a * (Finset.univ.filter (fun j => σ j ≠ τ j)).card) / (2 * n) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h : ∀ j : Fin n, lb16_tf n Z τ (Sum.inl (j, true)) *
        (lb16_rf n Z a σ (Sum.inl (j, true)) * lb16_qf n Z (Sum.inl (j, true))) +
      lb16_tf n Z τ (Sum.inl (j, false)) *
        (lb16_rf n Z a σ (Sum.inl (j, false)) * lb16_qf n Z (Sum.inl (j, false)))
      = (if σ j = τ j then 1 + a else 1 - a) / (2 * n) := by
    intro j
    simp only [lb16_tf, lb16_rf, lb16_qf, Sum.elim_inl]
    rcases Bool.eq_false_or_eq_true (σ j) with h | h <;>
      rcases Bool.eq_false_or_eq_true (τ j) with h' | h' <;> simp [h, h'] <;> field_simp
  rw [Fintype.sum_sum_type, lb16_sum_FB, Finset.sum_congr rfl (fun j _ => h j)]
  simp only [lb16_tf, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_div, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j : Fin n => σ j = τ j)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hc' : ((Finset.univ.filter (fun j => σ j = τ j)).card : ℝ)
      = n - (Finset.univ.filter (fun j => ¬ σ j = τ j)).card := by
    have : ((Finset.univ.filter (fun j => σ j = τ j)).card : ℝ)
        + (Finset.univ.filter (fun j => ¬ σ j = τ j)).card = n := by exact_mod_cast hc
    linarith
  rw [hc']
  simp only [ne_eq]
  ring

lemma lb16_ball (n : ℕ) (σ₀ : Fin n → Bool) :
    ((Finset.univ.filter (fun σ : Fin n → Bool =>
        3 * (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card ≤ n)).card : ℝ) ≤ (189 / 100 : ℝ) ^ n := by
  have hpt : ∀ σ : Fin n → Bool,
      (if 3 * (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card ≤ n then (1 : ℝ) else 0) ≤
        (5 / 4 : ℝ) ^ n * ∏ j, (if σ j ≠ σ₀ j then (64 / 125 : ℝ) else 1) := by
    intro σ
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    split_ifs with h
    · set d := (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card
      calc (1 : ℝ) = (125 / 64 : ℝ) ^ d * (64 / 125) ^ d := by rw [← mul_pow]; norm_num
        _ = (5 / 4 : ℝ) ^ (3 * d) * (64 / 125) ^ d := by rw [pow_mul]; norm_num
        _ ≤ (5 / 4 : ℝ) ^ n * (64 / 125) ^ d := by
            gcongr
            · norm_num
    · positivity
  calc _ = ∑ σ : Fin n → Bool,
        (if 3 * (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card ≤ n then (1 : ℝ) else 0) := by
        rw [Finset.sum_boole]
    _ ≤ ∑ σ : Fin n → Bool, (5 / 4 : ℝ) ^ n * ∏ j, (if σ j ≠ σ₀ j then (64 / 125 : ℝ) else 1) :=
        Finset.sum_le_sum (fun σ _ => hpt σ)
    _ = (5 / 4 : ℝ) ^ n * ∏ j : Fin n, ∑ b : Bool, (if b ≠ σ₀ j then (64 / 125 : ℝ) else 1) := by
        rw [← Finset.mul_sum, Fintype.prod_sum]
    _ = (189 / 100 : ℝ) ^ n := by
        have : ∀ j : Fin n, ∑ b : Bool, (if b ≠ σ₀ j then (64 / 125 : ℝ) else 1) = 189 / 125 := by
          intro j; rw [Fintype.sum_bool]; cases σ₀ j <;> norm_num
        simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← mul_pow]; norm_num

end ShadowTomography.ClassicalLB

open ShadowTomography.ClassicalLB in
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (D M : ℕ) (ε : ℝ),
      N₀ ≤ D → (N₀ : ℝ) ≤ Real.logb 2 M → 0 < ε → ε ≤ 1 / 6 →
      ∃ E : Fin M → Matrix (Fin D) (Fin D) ℂ,
            (∀ i, IsEffect (E i) ∧ (E i).IsDiag ∧
              ∀ x : Fin D, (E i) x x = 0 ∨ (E i) x x = 1) ∧
        ∀ (k : ℕ) (Ω : Type) [Fintype Ω]
          (P : POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
          (∀ ρ : Matrix (Fin D) (Fin D) ℂ,
            WildeQIT.IsDensityOperator ρ → ρ.IsDiag →
              (2 / 3 : ℝ) ≤ P.prob (tensorPow ρ k)
                (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε)) →
          c * min (D : ℝ) (Real.logb 2 M) / ε ^ 2 ≤ (k : ℝ) := by
  refine ⟨1 / 3000, by norm_num, 100, ?_⟩
  intro D M ε hD hM hε hε6
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = min (D / 2) (Nat.log 2 M) := ⟨_, rfl⟩
  have hn2 : 2 * n ≤ D := by
    have := min_le_left (D / 2) (Nat.log 2 M); omega
  have hnl : n ≤ Nat.log 2 M := hn ▸ min_le_right _ _
  have hpow : 2 ^ n ≤ M :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hnl) (Nat.pow_log_le_self 2 hM0)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hlog : Real.logb 2 M < (Nat.log 2 M : ℝ) + 1 := by
    have h1 : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    have h2 : (M : ℝ) < (2 : ℝ) ^ ((Nat.log 2 M : ℝ) + 1) := by
      rw [show ((Nat.log 2 M : ℝ) + 1) = ((Nat.log 2 M + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      exact_mod_cast h1
    exact (Real.logb_lt_iff_lt_rpow (by norm_num) hMpos).2 h2
  have hm100 : (100 : ℝ) ≤ min (D : ℝ) (Real.logb 2 M) :=
    le_min (by exact_mod_cast hD) (by exact_mod_cast hM)
  have hnm : min (D : ℝ) (Real.logb 2 M) / 2 ≤ n + 1 := by
    rcases le_total (D / 2) (Nat.log 2 M) with h | h
    · have hn' : n = D / 2 := by rw [hn, min_eq_left h]
      have h3 : D ≤ 2 * n + 1 := by omega
      have h4 : (D : ℝ) ≤ 2 * n + 1 := by exact_mod_cast h3
      have := min_le_left (D : ℝ) (Real.logb 2 M)
      linarith
    · have hn' : n = Nat.log 2 M := by rw [hn, min_eq_right h]
      have := min_le_right (D : ℝ) (Real.logb 2 M)
      rw [hn']
      linarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have e1 : Fintype.card ((Fin n × Bool) ⊕ Fin (D - 2 * n)) = Fintype.card (Fin D) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; omega
  have e2 : Fintype.card ((Fin n → Bool) ⊕ Fin (M - 2 ^ n)) = Fintype.card (Fin M) := by
    simp only [Fintype.card_sum, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.add_sub_of_le hpow
  obtain ⟨φ⟩ : Nonempty (Fin D ≃ (Fin n × Bool) ⊕ Fin (D - 2 * n)) :=
    ⟨(Fintype.equivOfCardEq e1).symm⟩
  obtain ⟨χ⟩ : Nonempty (Fin M ≃ (Fin n → Bool) ⊕ Fin (M - 2 ^ n)) :=
    ⟨(Fintype.equivOfCardEq e2).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 6 * ε := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  obtain ⟨c, hcdef⟩ : ∃ c : Fin M → Fin D → ℝ, c = fun m y =>
      Sum.elim (fun τ => lb16_tf n (Fin (D - 2 * n)) τ (φ y)) (fun _ => (0 : ℝ)) (χ m) := ⟨_, rfl⟩
  have hc01 : ∀ m y, c m y = 0 ∨ c m y = 1 := by
    intro m y
    simp only [hcdef]
    generalize χ m = s
    rcases s with τ | u
    · simp only [Sum.elim_inl]
      generalize φ y = t
      rcases t with ⟨j, bb⟩ | v
      · simp only [lb16_tf, Sum.elim_inl]; split_ifs <;> simp
      · simp [lb16_tf]
    · simp
  have hcm : ∀ τ y, c (χ.symm (Sum.inl τ)) y = lb16_tf n (Fin (D - 2 * n)) τ (φ y) := by
    intro τ y; rw [hcdef]; simp
  refine ⟨fun m => Matrix.diagonal (fun y => ((c m y : ℝ) : ℂ)), fun m => lb16_eff01 (c m) (hc01 m), ?_⟩
  intro k Ω _ P b hP
  obtain ⟨q, hqdef⟩ : ∃ q : Fin D → ℝ, q = fun y => lb16_qf n (Fin (D - 2 * n)) (φ y) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : (Fin n → Bool) → Fin D → ℝ,
      r = fun σ y => lb16_rf n (Fin (D - 2 * n)) a σ (φ y) := ⟨_, rfl⟩
  have hq0 : ∀ y, 0 ≤ q y := by
    intro y; rw [hqdef]; simp only
    generalize φ y = s
    rcases s with z | z <;> simp [lb16_qf]
  have hr0 : ∀ σ y, 0 ≤ r σ y := by
    intro σ y; rw [hrdef]; simp only
    generalize φ y = s
    rcases s with z | z
    · simp only [lb16_rf, Sum.elim_inl]; split_ifs <;> linarith
    · simp [lb16_rf]
  have hq1 : ∑ y, q y = 1 := by
    rw [hqdef]; simp only
    rw [Equiv.sum_comp φ (lb16_qf n (Fin (D - 2 * n)))]
    exact lb16_sum_qf n _ hn0
  have hrq1 : ∀ σ, ∑ y, r σ y * q y = 1 := by
    intro σ; rw [hrdef, hqdef]; simp only
    rw [Equiv.sum_comp φ (fun s => lb16_rf n (Fin (D - 2 * n)) a σ s * lb16_qf n (Fin (D - 2 * n)) s)]
    exact lb16_sum_rq n _ hn0 a σ
  have hX : ∀ σ, ∑ y, (r σ y) ^ 2 * q y = 1 + a ^ 2 := by
    intro σ; rw [hrdef, hqdef]; simp only
    rw [Equiv.sum_comp φ (fun s => (lb16_rf n (Fin (D - 2 * n)) a σ s) ^ 2 * lb16_qf n (Fin (D - 2 * n)) s)]
    exact lb16_sum_r2q n _ hn0 a σ
  have htr : ∀ τ σ, ((Matrix.diagonal (fun y => ((c (χ.symm (Sum.inl τ)) y : ℝ) : ℂ))) *
      Matrix.diagonal (fun y => ((r σ y * q y : ℝ) : ℂ))).trace.re
      = ((n : ℝ) * (1 + a) - 2 * a * (Finset.univ.filter (fun j => σ j ≠ τ j)).card) / (2 * n) := by
    intro τ σ
    rw [lb16_trace_diag]
    simp only [hcm]
    rw [hrdef, hqdef]; simp only
    rw [Equiv.sum_comp φ (fun s => lb16_tf n (Fin (D - 2 * n)) τ s *
      (lb16_rf n (Fin (D - 2 * n)) a σ s * lb16_qf n (Fin (D - 2 * n)) s))]
    exact lb16_sum_trq n _ hn0 a τ σ
  have hclose : ∀ ω σ₀ σ,
      (∀ i, |b ω i - ((Matrix.diagonal (fun y => ((c i y : ℝ) : ℂ))) *
        Matrix.diagonal (fun y => ((r σ₀ y * q y : ℝ) : ℂ))).trace.re| ≤ ε) →
      (∀ i, |b ω i - ((Matrix.diagonal (fun y => ((c i y : ℝ) : ℂ))) *
        Matrix.diagonal (fun y => ((r σ y * q y : ℝ) : ℂ))).trace.re| ≤ ε) →
      3 * (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card ≤ n := by
    intro ω σ₀ σ h0 h1
    have a0 := h0 (χ.symm (Sum.inl σ₀))
    have a1 := h1 (χ.symm (Sum.inl σ₀))
    rw [htr] at a0 a1
    have hd0 : (Finset.univ.filter (fun j => σ₀ j ≠ σ₀ j)).card = 0 := by simp
    rw [hd0] at a0
    set d : ℝ := ((Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card : ℝ) with hd
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hdiff : ((n : ℝ) * (1 + a) - 2 * a * ((0 : ℕ) : ℝ)) / (2 * n)
        - ((n : ℝ) * (1 + a) - 2 * a * d) / (2 * n) = a * d / n := by
      field_simp; ring
    have hle : a * d / n ≤ 2 * ε := by
      rw [← hdiff]
      have := (abs_le.mp a0); have := (abs_le.mp a1)
      linarith
    rw [div_le_iff₀ hnr] at hle
    have h3 : 3 * d ≤ n := by
      rw [ha] at hle
      nlinarith
    have : ((3 * (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hmain := lb16_core P q hq0 hq1 r (1 + a ^ 2) ((189 / 100 : ℝ) ^ n) hX (by positivity)
    (fun σ ω => ∀ i, |b ω i - ((Matrix.diagonal (fun y => ((c i y : ℝ) : ℂ))) *
        Matrix.diagonal (fun y => ((r σ y * q y : ℝ) : ℂ))).trace.re| ≤ ε) ?hL
    (fun σ => hP _ (lb16_dens _ (fun y => mul_nonneg (hr0 σ y) (hq0 y)) (hrq1 σ))
      (Matrix.isDiag_diagonal _))
  case hL =>
    intro ω
    by_cases hex : ∃ σ₀, ∀ i, |b ω i - ((Matrix.diagonal (fun y => ((c i y : ℝ) : ℂ))) *
        Matrix.diagonal (fun y => ((r σ₀ y * q y : ℝ) : ℂ))).trace.re| ≤ ε
    · obtain ⟨σ₀, h0⟩ := hex
      calc _ ≤ ((Finset.univ.filter (fun σ : Fin n → Bool =>
              3 * (Finset.univ.filter (fun j => σ j ≠ σ₀ j)).card ≤ n)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (fun σ hσ => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
              exact hclose ω σ₀ σ h0 hσ)
        _ ≤ _ := lb16_ball n σ₀
    · calc _ ≤ ((∅ : Finset (Fin n → Bool)).card : ℝ) := by
            norm_cast
            apply Finset.card_le_card
            intro σ hσ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
            exact absurd hσ (not_exists.mp hex σ)
        _ ≤ _ := by simp only [Finset.card_empty, Nat.cast_zero]; positivity
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hmain
  push_cast at hmain
  have hpos : (0 : ℝ) < 4 / 9 * 2 ^ n := by positivity
  have hl := Real.log_le_log hpos hmain
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hl
  have l1 : Real.log (1 + a ^ 2) ≤ a ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + a ^ 2 by positivity); linarith
  have l2 : Real.log (189 / 100 : ℝ) ≤ Real.log 2 - 11 / 200 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 189 / 200 by norm_num)
    have : Real.log (189 / 100 : ℝ) = Real.log 2 + Real.log (189 / 200) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    linarith
  have l3 : -(5 / 4 : ℝ) ≤ Real.log (4 / 9) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 9 by norm_num)
    norm_num at this; linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hn0' : (0 : ℝ) ≤ n := by positivity
  have m1 : (n : ℝ) * Real.log (189 / 100) ≤ n * Real.log 2 - n * (11 / 200) := by
    have := mul_le_mul_of_nonneg_left l2 hn0'; rwa [mul_sub] at this
  have m2 : (k : ℝ) * Real.log (1 + a ^ 2) ≤ k * a ^ 2 := mul_le_mul_of_nonneg_left l1 hk0
  have hk : (11 / 200) * (n : ℝ) - 5 / 4 ≤ 36 * ((k : ℝ) * ε ^ 2) := by
    have : (k : ℝ) * a ^ 2 = 36 * ((k : ℝ) * ε ^ 2) := by rw [ha]; ring
    linarith
  rw [div_le_iff₀ (by positivity)]
  linarith
