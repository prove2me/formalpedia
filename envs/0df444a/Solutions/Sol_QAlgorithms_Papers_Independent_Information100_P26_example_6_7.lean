-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.example_6_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:32:04.263993+00:00
-- url     : https://prove2.me/submissions/c6249bd4-8302-4d83-a39a-80ee8cd5b96f

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

/-- the example map, in terms of a real parameter -/
def x8t (d : ℕ) (a : ℝ) : Map d := a • transposition d + (1-a) • depolarizing d

theorem x8_t_apply {d : ℕ} (a : ℝ) (p q : Fin d × Fin d) :
    x8t d a p q = (a : ℂ) * (if p = (q.2, q.1) then 1 else 0) +
      ((1 - a : ℝ) : ℂ) * (if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0) := by
  simp [x8t, transposition, depolarizing, Complex.real_smul]

theorem x8_applyMap' {d : ℕ} (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ p : Fin d × Fin d, t (i, j) p * X p.1 p.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

theorem x8_t_act {d : ℕ} (a : ℝ) (X : Mat d) (i j : Fin d) :
    applyMap (x8t d a) X i j = (a : ℂ) * X j i +
      (if i = j then ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * X.trace else 0) := by
  rw [x8_applyMap']
  simp only [x8_t_apply, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp [Prod.ext_iff, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · rw [Fintype.sum_prod_type]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.trace, Matrix.diag, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mul_sum, mul_assoc]
    · simp [hij]

/-- symmetric/antisymmetric matrix-unit combination -/
def x8S {d : ℕ} (s : ℂ) (i j : Fin d) : Mat d := fun r u =>
  (if r = i ∧ u = j then 1 else 0) + s * (if r = j ∧ u = i then 1 else 0)

theorem x8_S_norm {d : ℕ} (s : ℂ) (hs : conj s = s) (hs2 : s * s = 1) (p q : Fin d) :
    ∑ i, ∑ j, (((x8S s i j)ᴴ * x8S s i j : Mat d)) p q =
      if p = q then 2 * (d : ℂ) + 2 * s else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, x8S, star_add, star_mul', hs,
    Complex.star_def, map_one, map_zero, apply_ite (starRingEnd ℂ), RCLike.star_def]
  simp only [hs, add_mul, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, ite_mul, mul_one,
    mul_zero, zero_mul, one_mul]
  by_cases hpq : p = q
  · subst hpq
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hs2, Finset.sum_add_distrib, @eq_comm _ p]
    ring
  · simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hpq, Ne.symm hpq]

theorem x8_S_act {d : ℕ} (s : ℂ) (hs : conj s = s) (hs2 : s * s = 1) (X : Mat d) (p q : Fin d) :
    ∑ i, ∑ j, ((x8S s i j * X * (x8S s i j)ᴴ : Mat d)) p q =
      2 * s * X q p + (if p = q then 2 * X.trace else 0) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, x8S, star_add, star_mul', hs,
    Complex.star_def, map_one, map_zero, apply_ite (starRingEnd ℂ), RCLike.star_def]
  simp only [hs, add_mul, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, ite_mul, mul_one,
    mul_zero, zero_mul, one_mul, Finset.sum_mul]
  by_cases hpq : p = q
  · subst hpq
    have hs2' : s ^ 2 = 1 := by rw [sq, hs2]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hs2', Matrix.trace, Matrix.diag,
      Finset.sum_add_distrib]
    have e : ∀ x, s * X x x * s = X x x := fun x => by linear_combination X x x * hs2
    simp only [e]
    ring
  · simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hpq, Ne.symm hpq, Matrix.trace]
    ring

theorem x8_isChannel_of' {A B κ : Type} [Fintype A] [Fintype B] [DecidableEq A] [Fintype κ]
    (Phi : Superop A B) (F : κ → Matrix B A ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1)
    (hPhi : ∀ X, Phi X = ∑ k, F k * X * (F k)ᴴ) : IsChannel Phi := by
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun n => F (e.symm n), ?_, fun X => ?_⟩
  · unfold IsKrausFamily; rw [← hF, ← e.symm.sum_comp]
  · rw [hPhi X, krausApply, ← e.symm.sum_comp]

def x8c (d : ℕ) (a : ℝ) (b : Bool) : ℂ :=
  if b then ((Real.sqrt (((1 - a) / d + a) / 4) : ℝ) : ℂ) else ((Real.sqrt (((1 - a) / d - a) / 4) : ℝ) : ℂ)

def x8sg (b : Bool) : ℂ := if b then 1 else -1

def x8K (d : ℕ) (a : ℝ) (k : Bool × Fin d × Fin d) : Mat d :=
  x8c d a k.1 • x8S (x8sg k.1) k.2.1 k.2.2

theorem x8_sg (b : Bool) : conj (x8sg b) = x8sg b ∧ x8sg b * x8sg b = 1 := by
  cases b <;> simp [x8sg]

theorem x8_c_sq {d : ℕ} (a : ℝ) (b : Bool) (hα : 0 ≤ (1 - a) / d + a) (hβ : 0 ≤ (1 - a) / d - a) :
    conj (x8c d a b) * x8c d a b =
      if b then ((((1 - a) / d + a) / 4 : ℝ) : ℂ) else ((((1 - a) / d - a) / 4 : ℝ) : ℂ) := by
  cases b
  · simp only [x8c, Bool.false_eq_true, if_false, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (by linarith)]
  · simp only [x8c, if_true, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (by linarith)]

theorem x8_K_norm {d : ℕ} (hd : 0 < d) (a : ℝ) (hα : 0 ≤ (1 - a) / d + a)
    (hβ : 0 ≤ (1 - a) / d - a) : ∑ k, (x8K d a k)ᴴ * x8K d a k = 1 := by
  ext p q
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ b : Bool, ∑ i, ∑ j, ((x8K d a (b, i, j))ᴴ * x8K d a (b, i, j)) p q =
      (conj (x8c d a b) * x8c d a b) * (if p = q then 2 * (d : ℂ) + 2 * x8sg b else 0) := by
    intro b
    rw [← x8_S_norm (x8sg b) (x8_sg b).1 (x8_sg b).2 p q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x8K, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_apply, smul_eq_mul, Complex.star_def]
    ring
  rw [h1, h1, x8_c_sq a true hα hβ, x8_c_sq a false hα hβ]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hpq : p = q
  · subst hpq
    simp [x8sg]
    field_simp
    ring
  · simp [hpq]

theorem x8_K_act {d : ℕ} (hd : 0 < d) (a : ℝ) (hα : 0 ≤ (1 - a) / d + a)
    (hβ : 0 ≤ (1 - a) / d - a) (X : Mat d) :
    applyMap (x8t d a) X = ∑ k, x8K d a k * X * (x8K d a k)ᴴ := by
  ext p q
  rw [x8_t_act, Matrix.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ b : Bool, ∑ i, ∑ j, ((x8K d a (b, i, j)) * X * (x8K d a (b, i, j))ᴴ) p q =
      (conj (x8c d a b) * x8c d a b) * (2 * x8sg b * X q p + (if p = q then 2 * X.trace else 0)) := by
    intro b
    rw [← x8_S_act (x8sg b) (x8_sg b).1 (x8_sg b).2 X p q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [x8K, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.smul_apply, smul_eq_mul, Complex.star_def]
    ring
  rw [h1, h1, x8_c_sq a true hα hβ, x8_c_sq a false hα hβ]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hpq : p = q
  · subst hpq
    simp [x8sg]
    field_simp
    ring
  · simp [hpq, x8sg]
    field_simp
    ring

theorem x8_unital {d : ℕ} (hd : 0 < d) (a : ℝ) (hα : 0 ≤ (1 - a) / d + a)
    (hβ : 0 ≤ (1 - a) / d - a) : UnitalChannel (x8t d a) := by
  refine ⟨x8_isChannel_of' _ (x8K d a) (x8_K_norm hd a hα hβ) (x8_K_act hd a hα hβ), ?_⟩
  ext i j
  rw [x8_t_act]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hij : i = j
  · subst hij
    simp [Matrix.trace_one]
    field_simp
    ring
  · simp [hij, Matrix.one_apply, Ne.symm hij]

theorem x8_mulT' {d : ℕ} (t : Map d) (p q : Fin d × Fin d) :
    (t * transposition d) p q = t p (q.2, q.1) := by
  rw [Matrix.mul_apply]
  simp [transposition]

theorem x8_ampT {d k : ℕ} (a : ℝ) (Z : Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ)
    (p q : Fin d × Fin k) :
    amplify (x8t d a * transposition d) k Z p q =
      (a : ℂ) * Z p q +
        (if p.1 = q.1 then ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * ∑ u, Z (u, p.2) (u, q.2) else 0) := by
  simp only [amplify, x8_mulT', x8_t_apply, Prod.mk.injEq, add_mul, Finset.sum_add_distrib, ite_and,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  congr 1
  · simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · by_cases h : p.1 = q.1
    · simp [h, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mul_sum, mul_assoc]
    · simp [h]

theorem x8_quad {d k : ℕ} (a : ℝ) (v w : Fin d × Fin k → ℂ) :
    star w ⬝ᵥ (amplify (x8t d a * transposition d) k (Matrix.vecMulVec v (star v)) *ᵥ w) =
      (a : ℂ) * ((∑ p, conj (w p) * v p) * (∑ q, conj (v q) * w q)) +
      ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * ∑ p1, ∑ u,
        (∑ j, conj (w (p1, j)) * v (u, j)) * (∑ j, conj (v (u, j)) * w (p1, j)) := by
  simp only [dotProduct, Matrix.mulVec, x8_ampT, Matrix.vecMulVec_apply, Pi.star_apply,
    add_mul, mul_add, Finset.sum_add_distrib, Complex.star_def]
  congr 1
  · rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  · simp only [ite_mul, zero_mul, mul_ite, mul_zero, Fintype.sum_prod_type]
    have hc : ∀ (F : Fin d → Fin k → ℂ) (x : Fin d),
        ∑ x2, ∑ x3, (if x = x2 then F x2 x3 else 0) = ∑ x3, F x x3 := by
      intro F x; rw [Finset.sum_comm]; simp
    simp only [hc]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p1 _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext p2; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q2 _ => ?_
    refine Finset.sum_congr rfl fun p2 _ => ?_
    ring

theorem x8_cs2 {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ x, a x * b x‖ ^ 2 ≤ (∑ x, ‖a x‖ ^ 2) * (∑ x, ‖b x‖ ^ 2) := by
  have h1 : ‖∑ x, a x * b x‖ ≤ ∑ x, ‖a x‖ * ‖b x‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => ‖a x‖) (fun x => ‖b x‖)
  calc ‖∑ x, a x * b x‖ ^ 2 ≤ (∑ x, ‖a x‖ * ‖b x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem x8_nsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.sq_norm]

theorem x8_rank2_orth {ι : Type*} [Fintype ι] (a0 a1 b0 b1 : ι → ℂ)
    (h : ∑ x, conj (a0 x) * a1 x = 0) :
    ‖∑ x, (a0 x * b0 x + a1 x * b1 x)‖ ^ 2 ≤
      2 * ∑ x, ∑ y, ‖a0 x * b0 y + a1 x * b1 y‖ ^ 2 := by
  have hS : ∑ x, ∑ y, ‖a0 x * b0 y + a1 x * b1 y‖ ^ 2 =
      (∑ x, ‖a0 x‖ ^ 2) * (∑ y, ‖b0 y‖ ^ 2) + (∑ x, ‖a1 x‖ ^ 2) * (∑ y, ‖b1 y‖ ^ 2) := by
    apply Complex.ofReal_injective
    have h' : ∑ x, a1 x * conj (a0 x) = 0 := by rw [← h]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    have h'' : ∑ x, a0 x * conj (a1 x) = 0 := by
      have := congrArg conj h'
      simp only [map_sum, map_mul, Complex.conj_conj, map_zero] at this
      rw [← this]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    simp only [Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul, x8_nsq, map_add, map_mul]
    calc ∑ x, ∑ y, (a0 x * b0 y + a1 x * b1 y) * (conj (a0 x) * conj (b0 y) + conj (a1 x) * conj (b1 y))
        = (∑ x, a0 x * conj (a0 x)) * (∑ y, b0 y * conj (b0 y)) +
          (∑ x, a1 x * conj (a1 x)) * (∑ y, b1 y * conj (b1 y)) +
          (∑ x, a0 x * conj (a1 x)) * (∑ y, b0 y * conj (b1 y)) +
          (∑ x, a1 x * conj (a0 x)) * (∑ y, b1 y * conj (b0 y)) := by
          simp only [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = _ := by rw [h', h'']; ring
  rw [hS]
  have c0 := x8_cs2 a0 b0
  have c1 := x8_cs2 a1 b1
  have tri : ‖∑ x, (a0 x * b0 x + a1 x * b1 x)‖ ≤ ‖∑ x, a0 x * b0 x‖ + ‖∑ x, a1 x * b1 x‖ := by
    rw [Finset.sum_add_distrib]; exact norm_add_le _ _
  have hn := norm_nonneg (∑ x, (a0 x * b0 x + a1 x * b1 x))
  nlinarith [sq_nonneg (‖∑ x, a0 x * b0 x‖ - ‖∑ x, a1 x * b1 x‖), norm_nonneg (∑ x, a0 x * b0 x),
    norm_nonneg (∑ x, a1 x * b1 x)]

theorem x8_rank2 {ι : Type*} [Fintype ι] (a0 a1 b0 b1 : ι → ℂ) :
    ‖∑ x, (a0 x * b0 x + a1 x * b1 x)‖ ^ 2 ≤
      2 * ∑ x, ∑ y, ‖a0 x * b0 y + a1 x * b1 y‖ ^ 2 := by
  set A : ℂ := ∑ x, conj (a0 x) * a0 x with hA
  set G : ℂ := ∑ x, conj (a0 x) * a1 x with hG
  by_cases hA0 : A = 0
  · have h0 : ∀ x, a0 x = 0 := by
      have hA' : ((∑ x, ‖a0 x‖ ^ 2 : ℝ) : ℂ) = A := by
        simp only [Complex.ofReal_sum, x8_nsq]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
      rw [hA0] at hA'
      have hr : ∑ x, ‖a0 x‖ ^ 2 = 0 := by exact_mod_cast hA'
      intro x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg ‖a0 x‖)).1 hr x (Finset.mem_univ _)
      simpa using this
    exact x8_rank2_orth a0 a1 b0 b1 (by simp [h0])
  · set l : ℂ := G / A
    have horth : ∑ x, conj (a0 x) * (a1 x - l * a0 x) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← hG]
      have : ∑ x, conj (a0 x) * (l * a0 x) = l * A := by
        rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      rw [this]; simp only [l]; field_simp; ring
    have := x8_rank2_orth a0 (fun x => a1 x - l * a0 x) (fun y => b0 y + l * b1 y) b1 horth
    have e1 : ∀ x y, a0 x * (b0 y + l * b1 y) + (a1 x - l * a0 x) * b1 y = a0 x * b0 y + a1 x * b1 y :=
      fun x y => by ring
    simp only [e1] at this
    exact this

theorem x8_amp_sum' {d k m : ℕ} (f : Map d) (Z : Fin m → Matrix (Fin d × Fin k) (Fin d × Fin k) ℂ) :
    amplify f k (∑ i, Z i) = ∑ i, amplify f k (Z i) := by
  ext p q
  simp only [amplify, Matrix.sum_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]

theorem x8_rank1_herm {d k : ℕ} (a : ℝ) (v : Fin d × Fin k → ℂ) :
    (amplify (x8t d a * transposition d) k (Matrix.vecMulVec v (star v))).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, x8_ampT, Matrix.vecMulVec_apply, Pi.star_apply,
    Complex.star_def]
  by_cases h : p.1 = q.1
  · simp only [h, if_true, map_add, map_mul, Complex.conj_ofReal, map_sum, Complex.conj_conj,
      map_inv₀, map_natCast]
    congr 1
    · ring
    · congr 1
      exact Finset.sum_congr rfl fun u _ => by ring
  · simp only [h, Ne.symm h, if_false, map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj,
      map_zero, add_zero]
    ring

theorem x8_rank1_nonneg {d : ℕ} (a : ℝ) (ha : a ≤ 0) (hc : -2 * a ≤ (1 - a) / d)
    (v w : Fin d × Fin 2 → ℂ) :
    0 ≤ star w ⬝ᵥ (amplify (x8t d a * transposition d) 2 (Matrix.vecMulVec v (star v)) *ᵥ w) := by
  rw [x8_quad]
  set T : ℂ := ∑ p, conj (w p) * v p with hT
  have hT' : ∑ q, conj (v q) * w q = conj T := by
    rw [hT, map_sum]; exact Finset.sum_congr rfl fun q _ => by simp [mul_comm]
  set M : Fin d → Fin d → ℂ := fun x y => ∑ j, conj (w (x, j)) * v (y, j) with hM
  have hM' : ∀ x y, ∑ j, conj (v (y, j)) * w (x, j) = conj (M x y) := by
    intro x y; simp only [hM, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp only [hT', hM']
  have hMM : ∀ x y, (∑ j, conj (w (x, j)) * v (y, j)) = M x y := fun x y => rfl
  simp only [hMM]
  have key : (a : ℂ) * (T * conj T) + ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * ∑ x, ∑ y, M x y * conj (M x y) =
      ((a * ‖T‖ ^ 2 + (1 - a) / d * ∑ x, ∑ y, ‖M x y‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum, x8_nsq, Complex.ofReal_div,
      Complex.ofReal_natCast, div_eq_mul_inv, Complex.ofReal_inv]
  rw [key]
  apply Complex.zero_le_real.mpr
  have hTM : ‖T‖ ^ 2 ≤ 2 * ∑ x, ∑ y, ‖M x y‖ ^ 2 := by
    have := x8_rank2 (fun x => conj (w (x, 0))) (fun x => conj (w (x, 1))) (fun y => v (y, 0))
      (fun y => v (y, 1))
    have e1 : T = ∑ x, (conj (w (x, 0)) * v (x, 0) + conj (w (x, 1)) * v (x, 1)) := by
      rw [hT, Fintype.sum_prod_type]; simp [Fin.sum_univ_two]
    have e2 : ∀ x y, M x y = conj (w (x, 0)) * v (y, 0) + conj (w (x, 1)) * v (y, 1) := by
      intro x y; simp [hM, Fin.sum_univ_two]
    rw [e1]; simp only [e2]; exact this
  have hS : 0 ≤ ∑ x, ∑ y, ‖M x y‖ ^ 2 := by positivity
  nlinarith

theorem x8_twoCop {d : ℕ} (a : ℝ) (ha : a ≤ 0) (hc : -2 * a ≤ (1 - a) / d) :
    TwoCopositive (x8t d a) := by
  intro Z hZ
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hZ
  rw [x8_amp_sum']
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  exact ⟨x8_rank1_herm a (v i), fun w => x8_rank1_nonneg a ha hc (v i) w⟩

theorem x8_notPPT {d : ℕ} (hd : 0 < d) (a : ℝ) (hneg : a * ((d : ℝ) ^ 2 - 1) < -1) :
    ¬ PPT (x8t d a) := by
  rintro ⟨-, hco⟩
  let Ω : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hZ := hco d hd (Matrix.vecMulVec Ω (star Ω)) (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hq := hZ.dotProduct_mulVec_nonneg Ω
  rw [x8_quad] at hq
  have e1 : ∑ p, conj (Ω p) * Ω p = (d : ℂ) := by
    rw [Fintype.sum_prod_type]; simp [Ω]
  have e2 : ∑ p, conj (Ω p) * Ω p = (d : ℂ) := e1
  have e3 : ∀ x y : Fin d, (∑ j, conj (Ω (x, j)) * Ω (y, j)) = if x = y then 1 else 0 := by
    intro x y; by_cases h : x = y
    · subst h; simp [Ω]
    · simp [Ω, h]
  have e4 : ∀ x y : Fin d, (∑ j, conj (Ω (y, j)) * Ω (x, j)) = if x = y then 1 else 0 := by
    intro x y; rw [e3 y x]; simp [eq_comm]
  simp only [e1, e3] at hq
  have e5 : (∑ x : Fin d, ∑ y : Fin d, (if x = y then (1 : ℂ) else 0) * (if y = x then 1 else 0)) = d := by
    simp [ite_mul, eq_comm]
  rw [e5] at hq
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (a : ℂ) * ((d : ℂ) * (d : ℂ)) + ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * (d : ℂ) =
      ((a * (d : ℝ) ^ 2 + (1 - a) : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [this] at hq
  have := Complex.zero_le_real.mp hq
  nlinarith

theorem x8_main {d : ℕ} (hd : 2 < d) (a : ℝ)
    (hlo : -(1 / (2*(d : ℝ)-1)) ≤ a) (hhi : a < -(1 / ((d : ℝ)^2-1))) :
    UnitalChannel (x8t d a) ∧ TwoCopositive (x8t d a) ∧ ¬ PPT (x8t d a) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h2 : (0 : ℝ) < 2 * (d : ℝ) - 1 := by linarith
  have h3 : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hlo' : -1 ≤ a * (2 * (d : ℝ) - 1) := by
    have := mul_le_mul_of_nonneg_right hlo h2.le
    rwa [neg_mul, one_div, inv_mul_cancel₀ h2.ne'] at this
  have hhi' : a * ((d : ℝ) ^ 2 - 1) < -1 := by
    have := mul_lt_mul_of_pos_right hhi h3
    rwa [neg_mul, one_div, inv_mul_cancel₀ h3.ne'] at this
  have ha : a < 0 := by
    by_contra h; push_neg at h; nlinarith
  have eα : (1 - a) / d + a = (1 + a * (d - 1)) / d := by field_simp; ring
  have eβ : (1 - a) / d - a = (1 - a * (d + 1)) / d := by field_simp; ring
  have eγ : (1 - a) / d + 2 * a = (1 + a * (2 * d - 1)) / d := by field_simp; ring
  have hα : 0 ≤ (1 - a) / d + a := by rw [eα]; apply div_nonneg _ hd0.le; nlinarith
  have hβ : 0 ≤ (1 - a) / d - a := by rw [eβ]; apply div_nonneg _ hd0.le; nlinarith
  have hc : -2 * a ≤ (1 - a) / d := by
    have : 0 ≤ (1 - a) / d + 2 * a := by rw [eγ]; apply div_nonneg _ hd0.le; linarith
    linarith
  exact ⟨x8_unital (by omega) a hα hβ, x8_twoCop a ha.le hc, x8_notPPT (by omega) a hhi'⟩

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 2 < d) (a : ℝ)
    (hlo : -(1 / (2*(d : ℝ)-1)) ≤ a) (hhi : a < -(1 / ((d : ℝ)^2-1))) :
    let t : Map d := a • transposition d + (1-a) • depolarizing d
    UnitalChannel t ∧ TwoCopositive t ∧ ¬ PPT t :=
  x8_main hd a hlo hhi
