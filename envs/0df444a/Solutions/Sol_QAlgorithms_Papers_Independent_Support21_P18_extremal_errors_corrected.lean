-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P18.extremal_errors_corrected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:59:04.353752+00:00
-- url     : https://prove2.me/submissions/7029e066-a362-4939-974a-0f1b3f32a908

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

lemma g71g1_traceRight_pure {α β γ : Type*} [Fintype β] [Fintype γ]
    (V : Matrix (α × β) γ ℂ) (v : EuclideanSpace ℂ γ) (a b : α) :
    traceRight (V * pureDensity v * Vᴴ) a b =
      ∑ h, (V.mulVec (WithLp.ofLp v)) (a, h) * conj ((V.mulVec (WithLp.ofLp v)) (b, h)) := by
  simp only [traceRight, Matrix.of_apply, Matrix.mul_apply, pureDensity, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun h _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring_nf
  done

lemma g71g1_sum_binom (n : ℕ) (X Y : ℂ) :
    ∑ k : Fin (n + 1), (n.choose k.val : ℂ) * X ^ (n - k.val) * Y ^ k.val = (X + Y) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℂ) * X ^ (n - k) * Y ^ k), add_pow,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp at hk
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega, Nat.choose_symm hk]
  ring

lemma g71g1_coef_low0 (n j : ℕ) (hj : j ≤ n) :
    Real.sqrt (((n + 1 - j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * Real.sqrt ((n + 1).choose j : ℝ) =
      Real.sqrt (n.choose j : ℝ) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have h := Nat.choose_mul_succ_eq n j
  have h' : ((n.choose j : ℕ) : ℝ) * (n + 1) = ((n + 1).choose j : ℕ) * ((n + 1 - j : ℕ) : ℝ) := by
    exact_mod_cast h
  field_simp
  push_cast at h' ⊢
  linarith

lemma g71g1_coef_low1 (n j : ℕ) :
    Real.sqrt (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) * Real.sqrt ((n + 1).choose (j + 1) : ℝ) =
      Real.sqrt (n.choose j : ℝ) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have h := Nat.add_one_mul_choose_eq n j
  have h' : ((n + 1 : ℕ) : ℝ) * (n.choose j : ℕ) = ((n + 1).choose (j + 1) : ℕ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  field_simp
  push_cast at h' ⊢
  linarith

lemma g71g1_lower_mulVec (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (a : Fin 2)
    (j : SymmetricBasis (n + 1 - 1)) :
    (lowerIsometry (n + 1)).mulVec (WithLp.ofLp (symmetricQubitKet (n + 1) ψ)) (a, j) =
      ψ a * symmetricQubitKet n ψ ⟨j.val, by omega⟩ := by
  have hj : j.val ≤ n := by omega
  simp only [Matrix.mulVec, dotProduct, lowerIsometry, symmetricQubitKet]
  fin_cases a
  · rw [Finset.sum_eq_single (⟨j.val, by omega⟩ : Fin (n + 1 + 1))]
    · rw [if_pos ⟨rfl, rfl⟩]
      dsimp only
      simp only [Fin.zero_eta]
      have := g71g1_coef_low0 n j.val hj
      have e : n + 1 - j.val = (n - j.val) + 1 := by omega
      rw [e, pow_succ]
      have hc : ((Real.sqrt (((n - j.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
          (Real.sqrt ((n + 1).choose j.val : ℝ) : ℂ) = (Real.sqrt (n.choose j.val : ℝ) : ℂ) := by
        rw [← e]; exact_mod_cast this
      push_cast at hc ⊢
      linear_combination (ψ 0 ^ (n - j.val) * ψ 0 * ψ 1 ^ j.val) * hc
    · intro b _ hb
      have : ¬ (j.val = b.val) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  · rw [Finset.sum_eq_single (⟨j.val + 1, by omega⟩ : Fin (n + 1 + 1))]
    · simp only [Fin.isValue]
      have := g71g1_coef_low1 n j.val
      have e : n + 1 - (j.val + 1) = n - j.val := by omega
      rw [if_neg (by simp), if_pos ⟨rfl, trivial⟩]
      simp only [Fin.mk_one]
      rw [e, pow_succ]
      have hc : ((Real.sqrt (((j.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
          (Real.sqrt ((n + 1).choose (j.val + 1) : ℝ) : ℂ) = (Real.sqrt (n.choose j.val : ℝ) : ℂ) := by
        exact_mod_cast this
      push_cast at hc ⊢
      linear_combination (ψ 0 ^ (n - j.val) * ψ 1 * ψ 1 ^ j.val) * hc
    · intro b _ hb
      have : ¬ (j.val + 1 = b.val) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp

lemma g71g1_state (ψ : EuclideanSpace ℂ (Fin 2)) (h : IsState ψ) :
    ψ 0 * conj (ψ 0) + ψ 1 * conj (ψ 1) = 1 := by
  unfold IsState at h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two] at h
  rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [← Complex.ofReal_add, h, Complex.ofReal_one]

lemma g71g1_sqrt_conj (r : ℝ) (hr : 0 ≤ r) :
    (Real.sqrt r : ℂ) * conj (Real.sqrt r : ℂ) = r := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hr]

lemma g71g1_symket_normsq (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) :
    ∑ j : Fin (n + 1), symmetricQubitKet n ψ j * conj (symmetricQubitKet n ψ j) =
      (ψ 0 * conj (ψ 0) + ψ 1 * conj (ψ 1)) ^ n := by
  rw [← g71g1_sum_binom]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [symmetricQubitKet, map_mul, map_pow]
  have := g71g1_sqrt_conj (n.choose k.val : ℝ) (by positivity)
  push_cast at this
  rw [mul_pow, mul_pow]
  linear_combination (ψ 0 ^ (n - k.val) * ψ 1 ^ k.val * conj (ψ 0) ^ (n - k.val) *
    conj (ψ 1) ^ k.val) * this

lemma g71g1_lower_out (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    lowerChannel (n + 1) (pureDensity (symmetricQubitKet (n + 1) ψ)) = pureDensity ψ := by
  ext a b
  unfold lowerChannel
  rw [g71g1_traceRight_pure]
  simp only [g71g1_lower_mulVec]
  have : ∀ h : Fin (n + 1 - 1 + 1),
      ψ a * symmetricQubitKet n ψ ⟨h.val, by omega⟩ * conj (ψ b * symmetricQubitKet n ψ ⟨h.val, by omega⟩)
      = ψ a * conj (ψ b) * (symmetricQubitKet n ψ ⟨h.val, by omega⟩ *
          conj (symmetricQubitKet n ψ ⟨h.val, by omega⟩)) := by
    intro h; simp only [map_mul]; ring
  rw [Finset.sum_congr rfl (fun h _ => this h), ← Finset.mul_sum]
  have hs : (∑ h : Fin (n + 1 - 1 + 1), symmetricQubitKet n ψ ⟨h.val, by omega⟩ *
          conj (symmetricQubitKet n ψ ⟨h.val, by omega⟩)) =
      ∑ h : Fin (n + 1), symmetricQubitKet n ψ h * conj (symmetricQubitKet n ψ h) := rfl
  rw [hs, g71g1_symket_normsq, g71g1_state ψ hψ, one_pow, mul_one]
  rfl

lemma g71g1_upper_mulVec0 (N : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (j : Fin (N + 2)) :
    (upperIsometry N).mulVec (WithLp.ofLp (symmetricQubitKet N ψ)) (0, j) =
      (Real.sqrt ((j.val : ℝ) / (N + 2)) : ℂ) * (Real.sqrt (N.choose (j.val - 1) : ℝ) : ℂ) *
        ψ 0 ^ (N - (j.val - 1)) * ψ 1 ^ (j.val - 1) := by
  simp only [Matrix.mulVec, dotProduct, upperIsometry, symmetricQubitKet]
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · rw [h0]
    simp
  · rw [Finset.sum_eq_single (⟨j.val - 1, by omega⟩ : Fin (N + 1))]
    · rw [if_pos (by simp; omega)]
      have e : ((j.val - 1 : ℕ) : ℝ) + 1 = (j.val : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      simp only [e]
      ring
    · intro b _ hb
      have : ¬ (j.val = b.val + 1) := fun h => hb (Fin.ext (by simp; omega))
      simp [this]
    · simp

lemma g71g1_upper_mulVec1 (N : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (j : Fin (N + 2)) :
    (upperIsometry N).mulVec (WithLp.ofLp (symmetricQubitKet N ψ)) (1, j) =
      -((Real.sqrt ((((N - j.val : ℕ) : ℝ) + 1) / (N + 2)) : ℂ) *
        (Real.sqrt (N.choose j.val : ℝ) : ℂ) * ψ 0 ^ (N - j.val) * ψ 1 ^ j.val) := by
  simp only [Matrix.mulVec, dotProduct, upperIsometry, symmetricQubitKet]
  rcases Nat.lt_or_ge N j.val with hgt | hle
  · rw [Nat.choose_eq_zero_of_lt hgt]
    simp
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (j.val = k.val) := by omega
    simp [this]
  · rw [Finset.sum_eq_single (⟨j.val, by omega⟩ : Fin (N + 1))]
    · rw [if_neg (by simp), if_pos (by simp)]
      ring
    · intro b _ hb
      have : ¬ (j.val = b.val) := fun h => hb (Fin.ext (by simp; omega))
      simp [this]
    · simp

lemma g71g1_sum_kbinom (n : ℕ) (X Y : ℂ) :
    ∑ k : Fin (n + 2), (k.val : ℂ) * ((n + 1).choose k.val : ℂ) * X ^ (n + 1 - k.val) * Y ^ k.val
      = (n + 1) * Y * (X + Y) ^ n := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, Fin.val_succ]
  rw [← g71g1_sum_binom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := Nat.add_one_mul_choose_eq n m.val
  have h' : ((n + 1 : ℕ) : ℂ) * (n.choose m.val : ℕ) = ((n + 1).choose (m.val + 1) : ℕ) * ((m.val + 1 : ℕ) : ℂ) := by
    exact_mod_cast h
  rw [show n + 1 - (m.val + 1) = n - m.val by omega, pow_succ]
  push_cast at h' ⊢
  linear_combination (-(X ^ (n - m.val) * Y ^ m.val * Y)) * h'

lemma g71g1_upper_00 (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    upperChannel (n + 1) (pureDensity (symmetricQubitKet (n + 1) ψ)) 0 0 =
      complementOutput (n + 1) ψ 0 0 := by
  have hs := g71g1_state ψ hψ
  unfold upperChannel
  rw [g71g1_traceRight_pure]
  simp only [g71g1_upper_mulVec0]
  set X := ψ 0 * conj (ψ 0)
  set Y := ψ 1 * conj (ψ 1)
  have ht : ∀ j : Fin (n + 1 + 2),
      (Real.sqrt ((j.val : ℝ) / ((n + 1 : ℕ) + 2)) : ℂ) * (Real.sqrt ((n + 1).choose (j.val - 1) : ℝ) : ℂ) *
        ψ 0 ^ (n + 1 - (j.val - 1)) * ψ 1 ^ (j.val - 1) *
      conj ((Real.sqrt ((j.val : ℝ) / ((n + 1 : ℕ) + 2)) : ℂ) * (Real.sqrt ((n + 1).choose (j.val - 1) : ℝ) : ℂ) *
        ψ 0 ^ (n + 1 - (j.val - 1)) * ψ 1 ^ (j.val - 1)) =
      ((j.val : ℂ) / ((n + 1 : ℕ) + 2)) * ((n + 1).choose (j.val - 1) : ℂ) *
        X ^ (n + 1 - (j.val - 1)) * Y ^ (j.val - 1) := by
    intro j
    have h1 := g71g1_sqrt_conj ((j.val : ℝ) / ((n + 1 : ℕ) + 2)) (by positivity)
    have h2 := g71g1_sqrt_conj ((n + 1).choose (j.val - 1) : ℝ) (by positivity)
    simp only [map_mul, map_pow]
    push_cast at h1 h2 ⊢
    simp only [X, Y, mul_pow]
    linear_combination
      (ψ 0 ^ (n + 1 - (j.val - 1)) * ψ 1 ^ (j.val - 1) * conj (ψ 0) ^ (n + 1 - (j.val - 1)) *
        conj (ψ 1) ^ (j.val - 1)) *
      ((Real.sqrt ((n + 1).choose (j.val - 1) : ℝ) : ℂ) *
        conj (Real.sqrt ((n + 1).choose (j.val - 1) : ℝ) : ℂ) * h1 +
       ((j.val : ℂ) / ((n : ℂ) + 1 + 2)) * h2)
  rw [Finset.sum_congr rfl (fun j _ => ht j), Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, zero_mul, zero_add, Fin.val_succ,
    Nat.add_sub_cancel]
  have hA := g71g1_sum_kbinom n X Y
  have hB := g71g1_sum_binom (n + 1) X Y
  have hsum : ∑ k : Fin (n + 2), ((k.val + 1 : ℕ) : ℂ) / ((n + 1 : ℕ) + 2) *
      ((n + 1).choose k.val : ℂ) * X ^ (n + 1 - k.val) * Y ^ k.val =
      (1 / ((n + 1 : ℕ) + 2 : ℂ)) * ((∑ k : Fin (n + 2), (k.val : ℂ) * ((n + 1).choose k.val : ℂ) *
        X ^ (n + 1 - k.val) * Y ^ k.val) +
        ∑ k : Fin (n + 1 + 1), ((n + 1).choose k.val : ℂ) * X ^ (n + 1 - k.val) * Y ^ k.val) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [hsum, hA, hB, hs]
  simp only [complementOutput, orthogonalDensity, pureDensity, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply, smul_eq_mul]
  have hY : Y = 1 - X := by linear_combination hs
  rw [hY]
  have h3 : ((n : ℂ) + 1 + 2) ≠ 0 := by norm_cast
  push_cast
  field_simp
  ring

lemma g71g1_upper_11 (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    upperChannel (n + 1) (pureDensity (symmetricQubitKet (n + 1) ψ)) 1 1 =
      complementOutput (n + 1) ψ 1 1 := by
  have hs := g71g1_state ψ hψ
  unfold upperChannel
  rw [g71g1_traceRight_pure]
  simp only [g71g1_upper_mulVec1]
  set X := ψ 0 * conj (ψ 0)
  set Y := ψ 1 * conj (ψ 1)
  have ht : ∀ j : Fin (n + 1 + 2),
      -((Real.sqrt ((((n + 1 - j.val : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) + 2)) : ℂ) *
        (Real.sqrt ((n + 1).choose j.val : ℝ) : ℂ) * ψ 0 ^ (n + 1 - j.val) * ψ 1 ^ j.val) *
      conj (-((Real.sqrt ((((n + 1 - j.val : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) + 2)) : ℂ) *
        (Real.sqrt ((n + 1).choose j.val : ℝ) : ℂ) * ψ 0 ^ (n + 1 - j.val) * ψ 1 ^ j.val)) =
      ((((n + 1 - j.val : ℕ) : ℂ) + 1) / ((n + 1 : ℕ) + 2)) * ((n + 1).choose j.val : ℂ) *
        X ^ (n + 1 - j.val) * Y ^ j.val := by
    intro j
    have h1 := g71g1_sqrt_conj ((((n + 1 - j.val : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) + 2)) (by positivity)
    have h2 := g71g1_sqrt_conj ((n + 1).choose j.val : ℝ) (by positivity)
    simp only [map_mul, map_pow, map_neg]
    push_cast at h1 h2 ⊢
    simp only [X, Y, mul_pow]
    linear_combination
      (ψ 0 ^ (n + 1 - j.val) * ψ 1 ^ j.val * conj (ψ 0) ^ (n + 1 - j.val) *
        conj (ψ 1) ^ j.val) *
      ((Real.sqrt ((n + 1).choose j.val : ℝ) : ℂ) *
        conj (Real.sqrt ((n + 1).choose j.val : ℝ) : ℂ) * h1 +
       ((((n + 1 - j.val : ℕ) : ℂ) + 1) / ((n : ℂ) + 1 + 2)) * h2)
  rw [Finset.sum_congr rfl (fun j _ => ht j), Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, Nat.choose_succ_self, Nat.cast_zero, mul_zero,
    zero_mul, add_zero]
  have hA := g71g1_sum_kbinom n X Y
  have hB := g71g1_sum_binom (n + 1) X Y
  have hsum : ∑ k : Fin (n + 2), ((((n + 1 - k.val : ℕ) : ℂ) + 1) / ((n + 1 : ℕ) + 2)) *
      ((n + 1).choose k.val : ℂ) * X ^ (n + 1 - k.val) * Y ^ k.val =
      (1 / ((n + 1 : ℕ) + 2 : ℂ)) * (((n : ℂ) + 2) * (∑ k : Fin (n + 1 + 1), ((n + 1).choose k.val : ℂ) *
        X ^ (n + 1 - k.val) * Y ^ k.val) -
        ∑ k : Fin (n + 2), (k.val : ℂ) * ((n + 1).choose k.val : ℂ) * X ^ (n + 1 - k.val) * Y ^ k.val) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : k.val ≤ n + 1 := by omega
    rw [Nat.cast_sub hk]
    push_cast; ring
  rw [hsum, hA, hB, hs]
  simp only [complementOutput, orthogonalDensity, pureDensity, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply, smul_eq_mul]
  have h3 : ((n : ℂ) + 1 + 2) ≠ 0 := by norm_cast
  push_cast
  field_simp
  ring

lemma g71g1_upper_01 (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    upperChannel (n + 1) (pureDensity (symmetricQubitKet (n + 1) ψ)) 0 1 =
      complementOutput (n + 1) ψ 0 1 := by
  have hs := g71g1_state ψ hψ
  unfold upperChannel
  rw [g71g1_traceRight_pure]
  simp only [g71g1_upper_mulVec0, g71g1_upper_mulVec1]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, Real.sqrt_zero, Complex.ofReal_zero, zero_mul,
    zero_add, Fin.val_succ, Fin.coe_castSucc, Fin.val_last, Nat.choose_succ_self, mul_zero,
    neg_zero, map_zero, add_zero, Nat.add_sub_cancel]
  set X := ψ 0 * conj (ψ 0)
  set Y := ψ 1 * conj (ψ 1)
  have hr : ∀ k : ℕ, k ≤ n →
      Real.sqrt (((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 2)) * Real.sqrt ((n + 1).choose k : ℝ) *
        (Real.sqrt ((((n + 1 - (k + 1) : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) + 2)) *
          Real.sqrt ((n + 1).choose (k + 1) : ℝ)) =
      ((n : ℝ) + 1) * (n.choose k : ℝ) / ((n : ℝ) + 3) := by
    intro k hk
    have h1 := Nat.add_one_mul_choose_eq n k
    have h2 := Nat.choose_mul_succ_eq n k
    have h1' : ((n + 1 : ℕ) : ℝ) * (n.choose k : ℕ) = ((n + 1).choose (k + 1) : ℕ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h2' : ((n.choose k : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) = ((n + 1).choose k : ℕ) * ((n + 1 - k : ℕ) : ℝ) := by
      exact_mod_cast h2
    rw [show n + 1 - (k + 1) = n - k by omega] 
    rw [show n + 1 - k = n - k + 1 by omega] at h2'
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [show ((n : ℝ) + 1) * (n.choose k : ℝ) / ((n : ℝ) + 3) =
      Real.sqrt ((((n : ℝ) + 1) * (n.choose k : ℝ) / ((n : ℝ) + 3)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    congr 1
    have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
    push_cast at h1' h2' ⊢
    have key : ((k : ℝ) + 1) * ((n + 1).choose (k + 1) : ℝ) * ((((n - k : ℕ) : ℝ) + 1) * ((n + 1).choose k : ℝ))
        = (((n : ℝ) + 1) * (n.choose k : ℝ)) ^ 2 := by
      linear_combination (-((((n - k : ℕ) : ℝ) + 1) * ((n + 1).choose k : ℝ))) * h1' -
        (((n : ℝ) + 1) * (n.choose k : ℝ)) * h2'
    have e : ((n:ℝ) + 1 + 2) = (n + 3) := by ring
    rw [e, div_pow, ← key]
    field_simp
  have ht : ∀ x : Fin (n + 1),
      (Real.sqrt (((x.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 2)) : ℂ) * (Real.sqrt ((n + 1).choose x.val : ℝ) : ℂ) *
        ψ 0 ^ (n + 1 - x.val) * ψ 1 ^ x.val *
      conj (-((Real.sqrt ((((n + 1 - (x.val + 1) : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) + 2)) : ℂ) *
        (Real.sqrt ((n + 1).choose (x.val + 1) : ℝ) : ℂ) * ψ 0 ^ (n + 1 - (x.val + 1)) * ψ 1 ^ (x.val + 1))) =
      -((((n : ℝ) + 1) / ((n : ℝ) + 3) : ℝ) : ℂ) * (ψ 0 * conj (ψ 1)) *
        ((n.choose x.val : ℂ) * X ^ (n - x.val) * Y ^ x.val) := by
    intro x
    have hx : x.val ≤ n := by omega
    have hrC := hr x.val hx
    have hrC' : (Real.sqrt (((x.val + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 2)) : ℂ) *
        (Real.sqrt ((n + 1).choose x.val : ℝ) : ℂ) *
        ((Real.sqrt ((((n + 1 - (x.val + 1) : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) + 2)) : ℂ) *
          (Real.sqrt ((n + 1).choose (x.val + 1) : ℝ) : ℂ)) =
        ((((n : ℝ) + 1) * (n.choose x.val : ℝ) / ((n : ℝ) + 3) : ℝ) : ℂ) := by
      exact_mod_cast hrC
    simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal]
    rw [show n + 1 - (x.val + 1) = n - x.val by omega, show n + 1 - x.val = n - x.val + 1 by omega,
      pow_succ, pow_succ]
    simp only [X, Y, mul_pow]
    rw [show n + 1 - (x.val + 1) = n - x.val by omega] at hrC'
    push_cast at hrC' ⊢
    have h3 : ((n : ℂ) + 3) ≠ 0 := by norm_cast
    linear_combination (-(ψ 0 ^ (n - x.val) * ψ 0 * ψ 1 ^ x.val * conj (ψ 0) ^ (n - x.val) *
      conj (ψ 1) ^ x.val * conj (ψ 1))) * hrC'
  rw [Finset.sum_congr rfl (fun x _ => ht x), ← Finset.mul_sum, g71g1_sum_binom, hs]
  simp only [complementOutput, orthogonalDensity, pureDensity, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.of_apply, smul_eq_mul]
  have h3 : ((n : ℂ) + 3) ≠ 0 := by norm_cast
  have h3' : ((n : ℂ) + 1 + 2) ≠ 0 := by norm_cast
  push_cast
  field_simp
  ring

lemma g71g1_traceRight_pure_symm {α β γ : Type*} [Fintype β] [Fintype γ]
    (V : Matrix (α × β) γ ℂ) (v : EuclideanSpace ℂ γ) (a b : α) :
    traceRight (V * pureDensity v * Vᴴ) b a = conj (traceRight (V * pureDensity v * Vᴴ) a b) := by
  rw [g71g1_traceRight_pure, g71g1_traceRight_pure, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma g71g1_upper_out (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    upperChannel (n + 1) (pureDensity (symmetricQubitKet (n + 1) ψ)) = complementOutput (n + 1) ψ := by
  ext a b
  fin_cases a <;> fin_cases b
  · exact g71g1_upper_00 n ψ hψ
  · exact g71g1_upper_01 n ψ hψ
  · have h := g71g1_upper_01 n ψ hψ
    change traceRight _ 1 0 = _
    rw [g71g1_traceRight_pure_symm]
    change conj (upperChannel (n + 1) (pureDensity (symmetricQubitKet (n + 1) ψ)) 0 1) = _
    rw [h]
    simp [complementOutput, orthogonalDensity, pureDensity, Matrix.one_apply_ne, map_ofNat]
    ring_nf
    simp
  · exact g71g1_upper_11 n ψ hψ

lemma g71g1_effect_pure (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    effectProb (pureDensity ψ) (pureDensity ψ) = 1 := by
  have hs := g71g1_state ψ hψ
  have : (pureDensity ψ * pureDensity ψ).trace = 1 := by
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, pureDensity]
    linear_combination (ψ 0 * conj (ψ 0) + ψ 1 * conj (ψ 1) + 1) * hs
  simp [effectProb, this]

lemma g71g1_effect_comp (n : ℕ) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : IsState ψ) :
    effectProb (pureDensity ψ) (complementOutput n ψ) = 1 / ((n : ℝ) + 2) := by
  have hs := g71g1_state ψ hψ
  have h2 : ((n : ℂ) + 2) ≠ 0 := by norm_cast
  have : (pureDensity ψ * complementOutput n ψ).trace = 1 / ((n : ℂ) + 2) := by
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, pureDensity, complementOutput,
      orthogonalDensity, Matrix.one_apply]
    field_simp
    linear_combination (1 - (n : ℂ) * (ψ 0 * conj (ψ 0) + ψ 1 * conj (ψ 1))) * hs
  rw [effectProb, this]
  have : (1 / ((n : ℂ) + 2)) = ((1 / ((n : ℝ) + 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.ofReal_re]

lemma g71g1_exists_state : ∃ ψ : EuclideanSpace ℂ (Fin 2), IsState ψ :=
  ⟨EuclideanSpace.single 0 1, by simp [IsState]⟩

theorem solution (N : ℕ) (hN : 1 ≤ N) :
    notError N (lowerChannel N) = 1 ∧
    notError N (upperChannel N) = 1 / ((N : ℝ) + 2) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), IsState psi →
      lowerChannel N (pureDensity (symmetricQubitKet N psi)) = pureDensity psi ∧
      upperChannel N (pureDensity (symmetricQubitKet N psi)) = complementOutput N psi) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨ψ0, hψ0⟩ := g71g1_exists_state
  refine ⟨?_, ?_, fun psi hpsi => ⟨g71g1_lower_out n psi hpsi, g71g1_upper_out n psi hpsi⟩⟩
  · have : errorValues (n + 1) (lowerChannel (n + 1)) = {1} := by
      ext r
      simp only [errorValues, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨psi, hpsi, rfl⟩
        rw [g71g1_lower_out n psi hpsi, g71g1_effect_pure psi hpsi]
      · rintro rfl
        exact ⟨ψ0, hψ0, by rw [g71g1_lower_out n ψ0 hψ0, g71g1_effect_pure ψ0 hψ0]⟩
    rw [notError, this, csSup_singleton]
  · have : errorValues (n + 1) (upperChannel (n + 1)) = {1 / (((n + 1 : ℕ) : ℝ) + 2)} := by
      ext r
      simp only [errorValues, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨psi, hpsi, rfl⟩
        rw [g71g1_upper_out n psi hpsi, g71g1_effect_comp (n + 1) psi hpsi]
      · rintro rfl
        exact ⟨ψ0, hψ0, by rw [g71g1_upper_out n ψ0 hψ0, g71g1_effect_comp (n + 1) ψ0 hψ0]⟩
    rw [notError, this, csSup_singleton]
