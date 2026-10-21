-- Prove2me | solution 1 for QApproxCount.Counting.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:39:29.471274+00:00
-- url     : https://prove2.me/submissions/b15bad1b-981e-4215-a44a-d5cced3e9cee

import Mathlib
import Definitions.Def_QApproxCount_Counting_Grover
set_option autoImplicit false

open QApproxCount.Counting Matrix

noncomputable def vv {n : ℕ} (T : Finset (Fin n)) (φ : ℝ) : Fin n → ℂ :=
  fun x => if x ∈ T then ((Real.sin φ / Real.sqrt (T.card : ℝ) : ℝ) : ℂ)
    else ((Real.cos φ / Real.sqrt ((n : ℝ) - T.card) : ℝ) : ℂ)

lemma sum_ite_card {n : ℕ} (T : Finset (Fin n)) (A B : ℝ) :
    ∑ x : Fin n, (if x ∈ T then A else B) = T.card * A + ((n : ℝ) - T.card) * B := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have h1 : Finset.univ.filter (fun x : Fin n => x ∈ T) = T := by ext; simp
  have h2 : (Finset.univ.filter (fun x : Fin n => x ∉ T)).card = n - T.card := by
    rw [Finset.filter_not, h1, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [h1, h2]
  have : T.card ≤ n := by simpa using Finset.card_le_univ T
  rw [Nat.cast_sub this]

lemma trig1 (φ θ : ℝ) :
    Real.sin φ + 2 * Real.sin θ * Real.cos (φ + θ) = Real.sin (φ + 2 * θ) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [show φ + 2 * θ = (φ + θ) + θ by ring, Real.sin_add (φ + θ) θ, Real.sin_add, Real.cos_add]
  linear_combination (-Real.sin φ) * h

lemma trig2 (φ θ : ℝ) :
    Real.cos φ - 2 * Real.cos θ * Real.cos (φ + θ) = -Real.cos (φ + 2 * θ) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [show φ + 2 * θ = (φ + θ) + θ by ring, Real.cos_add (φ + θ) θ, Real.sin_add, Real.cos_add]
  linear_combination (-Real.cos φ) * h

lemma proj_apply {n : ℕ} (ψ w : Fin n → ℂ) (x : Fin n) :
    ((1 - (2 : ℂ) • vecMulVec ψ (star ψ)) *ᵥ w) x = w x - 2 * (ψ x * ∑ j, star (ψ j) * w j) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 2
  simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

lemma grover_step {n : ℕ} (T : Finset (Fin n)) (hT : 0 < T.card) (hTn : T.card < n) (φ : ℝ) :
    groverOp T *ᵥ vv T φ =
      -(vv T (φ + 2 * Real.arcsin (Real.sqrt ((T.card : ℝ) / n)))) := by
  set θ := Real.arcsin (Real.sqrt ((T.card : ℝ) / n)) with hθ
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT
  have htn' : (T.card : ℝ) < n := by exact_mod_cast hTn
  have hn : (0 : ℝ) < n := by linarith
  have htn : (0 : ℝ) < (n : ℝ) - T.card := by linarith
  set a := Real.sqrt (T.card : ℝ) with ha
  set b := Real.sqrt ((n : ℝ) - T.card) with hb
  set q := Real.sqrt (n : ℝ) with hq
  have ha0 : 0 < a := Real.sqrt_pos.2 ht
  have hb0 : 0 < b := Real.sqrt_pos.2 htn
  have hq0 : 0 < q := Real.sqrt_pos.2 hn
  have ha2 : a ^ 2 = T.card := Real.sq_sqrt ht.le
  have hb2 : b ^ 2 = (n : ℝ) - T.card := Real.sq_sqrt htn.le
  have hq2 : q ^ 2 = n := Real.sq_sqrt hn.le
  have hsin : Real.sin θ = a / q := by
    rw [hθ, Real.sin_arcsin, Real.sqrt_div ht.le]
    · exact le_trans (by linarith [Real.sqrt_nonneg ((T.card : ℝ) / n)]) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_one.mpr
      rw [div_le_one hn]; exact htn'.le
  have hcos : Real.cos θ = b / q := by
    rw [hθ, Real.cos_arcsin, Real.sq_sqrt (div_nonneg ht.le hn.le), ← Real.sqrt_div htn.le]
    congr 1
    field_simp
  have hs2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hq1 : q⁻¹ = Real.sin θ / a := by rw [hsin]; field_simp
  have hq2' : q⁻¹ = Real.cos θ / b := by rw [hcos]; field_simp
  have hw : phaseOracle T *ᵥ vv T φ = fun x =>
      if x ∈ T then ((-(Real.sin φ / a) : ℝ) : ℂ) else ((Real.cos φ / b : ℝ) : ℂ) := by
    funext x
    simp only [phaseOracle, Matrix.mulVec_diagonal, vv, ← ha, ← hb]
    split_ifs
    · rw [Complex.ofReal_neg]; ring
    · ring
  have hS : ∑ j, star (uniformState n j) * (phaseOracle T *ᵥ vv T φ) j =
      ((Real.cos (φ + θ) : ℝ) : ℂ) := by
    rw [hw]
    have : ∀ j : Fin n, star (uniformState n j) *
        (if j ∈ T then ((-(Real.sin φ / a) : ℝ) : ℂ) else ((Real.cos φ / b : ℝ) : ℂ)) =
        (((if j ∈ T then q⁻¹ * (-(Real.sin φ / a)) else q⁻¹ * (Real.cos φ / b) : ℝ)) : ℂ) := by
      intro j
      by_cases hj : j ∈ T <;> simp [hj, uniformState, hq]
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Complex.ofReal_sum, sum_ite_card]
    congr 1
    rw [Real.cos_add, hsin, hcos, ← hb2, ← ha2]
    field_simp
    ring
  funext x
  rw [groverOp, ← Matrix.mulVec_mulVec, proj_apply, hS]
  by_cases hx : x ∈ T
  · simp only [hw, hx, if_true, vv, Pi.neg_apply, uniformState]
    rw [← ha, ← hq]
    have h : (-(Real.sin φ / a) - 2 * (q⁻¹ * Real.cos (φ + θ)) : ℝ) =
        -(Real.sin (φ + 2 * θ) / a) := by
      rw [hq1, ← trig1 φ θ]; ring
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h' ⊢
    linear_combination h'
  · simp only [hw, hx, if_false, vv, Pi.neg_apply, uniformState]
    rw [← hb, ← hq]
    have h : (Real.cos φ / b - 2 * (q⁻¹ * Real.cos (φ + θ)) : ℝ) =
        -(Real.cos (φ + 2 * θ) / b) := by
      rw [hq2', ← neg_div, ← trig2 φ θ]; ring
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h' ⊢
    linear_combination h'

lemma uniform_eq {n : ℕ} (T : Finset (Fin n)) (hT : 0 < T.card) (hTn : T.card < n) :
    uniformState n = vv T (Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) := by
  set θ := Real.arcsin (Real.sqrt ((T.card : ℝ) / n)) with hθ
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT
  have htn' : (T.card : ℝ) < n := by exact_mod_cast hTn
  have hn : (0 : ℝ) < n := by linarith
  have htn : (0 : ℝ) < (n : ℝ) - T.card := by linarith
  have ha0 : 0 < Real.sqrt (T.card : ℝ) := Real.sqrt_pos.2 ht
  have hb0 : 0 < Real.sqrt ((n : ℝ) - T.card) := Real.sqrt_pos.2 htn
  have hq0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn
  have hsin : Real.sin θ = Real.sqrt (T.card : ℝ) / Real.sqrt (n : ℝ) := by
    rw [hθ, Real.sin_arcsin, Real.sqrt_div ht.le]
    · exact le_trans (by linarith [Real.sqrt_nonneg ((T.card : ℝ) / n)]) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_one.mpr
      rw [div_le_one hn]; exact htn'.le
  have hcos : Real.cos θ = Real.sqrt ((n : ℝ) - T.card) / Real.sqrt (n : ℝ) := by
    rw [hθ, Real.cos_arcsin, Real.sq_sqrt (div_nonneg ht.le hn.le), ← Real.sqrt_div htn.le]
    congr 1
    field_simp
  funext x
  simp only [uniformState, vv]
  split_ifs
  · rw [hsin]; congr 1; field_simp
  · rw [hcos]; congr 1; field_simp

lemma grover_pow {n : ℕ} (T : Finset (Fin n)) (hT : 0 < T.card) (hTn : T.card < n) (j : ℕ) :
    groverState T j =
      (-1 : ℂ) ^ j • vv T (((2 * j + 1 : ℕ) : ℝ) * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) := by
  set θ := Real.arcsin (Real.sqrt ((T.card : ℝ) / n)) with hθ
  induction j with
  | zero =>
    simp only [groverState, pow_zero, Matrix.one_mulVec, one_smul]
    rw [uniform_eq T hT hTn]
    congr 1
    push_cast; ring
  | succ j ih =>
    have e : groverState T (j + 1) = groverOp T *ᵥ groverState T j := by
      simp only [groverState, pow_succ', Matrix.mulVec_mulVec]
    rw [e, ih, Matrix.mulVec_smul, grover_step T hT hTn, smul_neg, pow_succ]
    have : ((2 * j + 1 : ℕ) : ℝ) * θ + 2 * θ = ((2 * (j + 1) + 1 : ℕ) : ℝ) * θ := by
      push_cast; ring
    rw [this, mul_neg_one, neg_smul]

theorem solution {n : ℕ} (T : Finset (Fin n)) (hT : 0 < T.card) (hTn : T.card < n)
    (r : ℕ) (hr : Odd r) :
    groverState T ((r - 1) / 2) =
        (fun x => (-1 : ℂ) ^ ((r - 1) / 2) *
          (if x ∈ T then
            ((Real.sin (r * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) /
              Real.sqrt (T.card : ℝ) : ℝ) : ℂ)
          else
            ((Real.cos (r * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) /
              Real.sqrt ((n : ℝ) - T.card) : ℝ) : ℂ))) ∧
      markedProb T ((r - 1) / 2) =
        Real.sin (r * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) ^ 2 := by
  obtain ⟨j, rfl⟩ := hr
  have hj : (2 * j + 1 - 1) / 2 = j := by omega
  rw [hj]
  have key := grover_pow T hT hTn j
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT
  constructor
  · rw [key]
    funext x
    simp only [vv, Pi.smul_apply, smul_eq_mul]
  · unfold markedProb
    rw [key]
    have hx : ∀ x ∈ T, ‖((-1 : ℂ) ^ j • vv T (((2 * j + 1 : ℕ) : ℝ) *
        Real.arcsin (Real.sqrt ((T.card : ℝ) / n)))) x‖ ^ 2 =
        Real.sin (((2 * j + 1 : ℕ) : ℝ) * Real.arcsin (Real.sqrt ((T.card : ℝ) / n))) ^ 2 /
          (T.card : ℝ) := by
      intro x hx
      simp only [vv, Pi.smul_apply, smul_eq_mul, hx, if_true, norm_mul, norm_pow, norm_neg,
        norm_one, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [div_pow, Real.sq_sqrt ht.le]
    rw [Finset.sum_congr rfl hx, Finset.sum_const, nsmul_eq_mul]
    field_simp
