-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.cliffordT_entry_rings
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:02:57.655711+00:00
-- url     : https://prove2.me/submissions/935f8d3b-8a1d-400c-a0f4-a9d05d143a1e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

def g73p_w : ℂ := QAlgorithms.gateT true true

def g73p_m (a b c d : ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i then (if j then d else c) else (if j then b else a)

theorem g73p_m_mul (a b c d e f g h : ℂ) :
    g73p_m a b c d * g73p_m e f g h =
      g73p_m (a * e + b * g) (a * f + b * h) (c * e + d * g) (c * f + d * h) := by
  ext i j; cases i <;> cases j <;> simp [g73p_m, Matrix.mul_apply] <;> ring

theorem g73p_m_ext {a b c d a' b' c' d' : ℂ} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : g73p_m a b c d = g73p_m a' b' c' d' := by subst h1 h2 h3 h4; rfl

theorem g73p_m_star (a b c d : ℂ) :
    star (g73p_m a b c d) = g73p_m (star a) (star c) (star b) (star d) := by
  ext i j; cases i <;> cases j <;> simp [g73p_m, Matrix.star_apply]

theorem g73p_w_eq : g73p_w =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have : g73p_w = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    simp [g73p_w, QAlgorithms.gateT]; ring_nf
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

theorem g73p_s2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp

theorem g73p_w2 : g73p_w ^ 2 = Complex.I := by
  rw [g73p_w_eq]; push_cast
  linear_combination ((1 + 2 * Complex.I + Complex.I ^ 2) / 4) * g73p_s2 + (1/2) * Complex.I_sq

theorem g73p_w4 : g73p_w ^ 4 = -1 := by
  rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, g73p_w2, Complex.I_sq]

theorem g73p_I : Complex.I = g73p_w ^ 2 := g73p_w2.symm

theorem g73p_sqrt2 : ((Real.sqrt 2 : ℝ) : ℂ) =
    g73p_w - g73p_w ^ 3 := by
  have h3 : g73p_w ^ 3 = g73p_w * Complex.I := by
    rw [← g73p_w2]; ring
  rw [h3, g73p_w_eq]; push_cast
  linear_combination ((Real.sqrt 2 : ℂ) / 2) * Complex.I_sq

theorem g73p_r : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) =
    (g73p_w - g73p_w ^ 3) / 2 := by
  rw [← g73p_sqrt2]
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have := g73p_s2; intro h0; rw [h0] at this; norm_num at this
  push_cast; field_simp; linear_combination (-1) * g73p_s2

theorem g73p_p4 : g73p_w ^ 4 = -1 := by
  linear_combination ((1) * g73p_w ^ 0) * g73p_w4

theorem g73p_p5 : g73p_w ^ 5 = -g73p_w := by
  linear_combination ((1) * g73p_w ^ 1) * g73p_w4

theorem g73p_p6 : g73p_w ^ 6 = -g73p_w ^ 2 := by
  linear_combination ((1) * g73p_w ^ 2) * g73p_w4

theorem g73p_p7 : g73p_w ^ 7 = -g73p_w ^ 3 := by
  linear_combination ((1) * g73p_w ^ 3) * g73p_w4

theorem g73p_p8 : g73p_w ^ 8 = 1 := by
  linear_combination ((-1) * g73p_w ^ 0 + (1) * g73p_w ^ 4) * g73p_w4

theorem g73p_p9 : g73p_w ^ 9 = g73p_w := by
  linear_combination ((-1) * g73p_w ^ 1 + (1) * g73p_w ^ 5) * g73p_w4

theorem g73p_p10 : g73p_w ^ 10 = g73p_w ^ 2 := by
  linear_combination ((-1) * g73p_w ^ 2 + (1) * g73p_w ^ 6) * g73p_w4

theorem g73p_p11 : g73p_w ^ 11 = g73p_w ^ 3 := by
  linear_combination ((-1) * g73p_w ^ 3 + (1) * g73p_w ^ 7) * g73p_w4

theorem g73p_p12 : g73p_w ^ 12 = -1 := by
  linear_combination ((1) * g73p_w ^ 0 + (-1) * g73p_w ^ 4 + (1) * g73p_w ^ 8) * g73p_w4

theorem g73p_p13 : g73p_w ^ 13 = -g73p_w := by
  linear_combination ((1) * g73p_w ^ 1 + (-1) * g73p_w ^ 5 + (1) * g73p_w ^ 9) * g73p_w4

theorem g73p_p14 : g73p_w ^ 14 = -g73p_w ^ 2 := by
  linear_combination ((1) * g73p_w ^ 2 + (-1) * g73p_w ^ 6 + (1) * g73p_w ^ 10) * g73p_w4

theorem g73p_p15 : g73p_w ^ 15 = -g73p_w ^ 3 := by
  linear_combination ((1) * g73p_w ^ 3 + (-1) * g73p_w ^ 7 + (1) * g73p_w ^ 11) * g73p_w4

theorem g73p_p16 : g73p_w ^ 16 = 1 := by
  linear_combination ((-1) * g73p_w ^ 0 + (1) * g73p_w ^ 4 + (-1) * g73p_w ^ 8 + (1) * g73p_w ^ 12) * g73p_w4

theorem g73p_p17 : g73p_w ^ 17 = g73p_w := by
  linear_combination ((-1) * g73p_w ^ 1 + (1) * g73p_w ^ 5 + (-1) * g73p_w ^ 9 + (1) * g73p_w ^ 13) * g73p_w4

theorem g73p_p18 : g73p_w ^ 18 = g73p_w ^ 2 := by
  linear_combination ((-1) * g73p_w ^ 2 + (1) * g73p_w ^ 6 + (-1) * g73p_w ^ 10 + (1) * g73p_w ^ 14) * g73p_w4

theorem g73p_p19 : g73p_w ^ 19 = g73p_w ^ 3 := by
  linear_combination ((-1) * g73p_w ^ 3 + (1) * g73p_w ^ 7 + (-1) * g73p_w ^ 11 + (1) * g73p_w ^ 15) * g73p_w4

theorem g73p_p20 : g73p_w ^ 20 = -1 := by
  linear_combination ((1) * g73p_w ^ 0 + (-1) * g73p_w ^ 4 + (1) * g73p_w ^ 8 + (-1) * g73p_w ^ 12 + (1) * g73p_w ^ 16) * g73p_w4

theorem g73p_p21 : g73p_w ^ 21 = -g73p_w := by
  linear_combination ((1) * g73p_w ^ 1 + (-1) * g73p_w ^ 5 + (1) * g73p_w ^ 9 + (-1) * g73p_w ^ 13 + (1) * g73p_w ^ 17) * g73p_w4

theorem g73p_p22 : g73p_w ^ 22 = -g73p_w ^ 2 := by
  linear_combination ((1) * g73p_w ^ 2 + (-1) * g73p_w ^ 6 + (1) * g73p_w ^ 10 + (-1) * g73p_w ^ 14 + (1) * g73p_w ^ 18) * g73p_w4

theorem g73p_p23 : g73p_w ^ 23 = -g73p_w ^ 3 := by
  linear_combination ((1) * g73p_w ^ 3 + (-1) * g73p_w ^ 7 + (1) * g73p_w ^ 11 + (-1) * g73p_w ^ 15 + (1) * g73p_w ^ 19) * g73p_w4

theorem g73p_p24 : g73p_w ^ 24 = 1 := by
  linear_combination ((-1) * g73p_w ^ 0 + (1) * g73p_w ^ 4 + (-1) * g73p_w ^ 8 + (1) * g73p_w ^ 12 + (-1) * g73p_w ^ 16 + (1) * g73p_w ^ 20) * g73p_w4

theorem g73p_p25 : g73p_w ^ 25 = g73p_w := by
  linear_combination ((-1) * g73p_w ^ 1 + (1) * g73p_w ^ 5 + (-1) * g73p_w ^ 9 + (1) * g73p_w ^ 13 + (-1) * g73p_w ^ 17 + (1) * g73p_w ^ 21) * g73p_w4

theorem g73p_p26 : g73p_w ^ 26 = g73p_w ^ 2 := by
  linear_combination ((-1) * g73p_w ^ 2 + (1) * g73p_w ^ 6 + (-1) * g73p_w ^ 10 + (1) * g73p_w ^ 14 + (-1) * g73p_w ^ 18 + (1) * g73p_w ^ 22) * g73p_w4

theorem g73p_p27 : g73p_w ^ 27 = g73p_w ^ 3 := by
  linear_combination ((-1) * g73p_w ^ 3 + (1) * g73p_w ^ 7 + (-1) * g73p_w ^ 11 + (1) * g73p_w ^ 15 + (-1) * g73p_w ^ 19 + (1) * g73p_w ^ 23) * g73p_w4

theorem g73p_p28 : g73p_w ^ 28 = -1 := by
  linear_combination ((1) * g73p_w ^ 0 + (-1) * g73p_w ^ 4 + (1) * g73p_w ^ 8 + (-1) * g73p_w ^ 12 + (1) * g73p_w ^ 16 + (-1) * g73p_w ^ 20 + (1) * g73p_w ^ 24) * g73p_w4

theorem g73p_p29 : g73p_w ^ 29 = -g73p_w := by
  linear_combination ((1) * g73p_w ^ 1 + (-1) * g73p_w ^ 5 + (1) * g73p_w ^ 9 + (-1) * g73p_w ^ 13 + (1) * g73p_w ^ 17 + (-1) * g73p_w ^ 21 + (1) * g73p_w ^ 25) * g73p_w4

theorem g73p_p30 : g73p_w ^ 30 = -g73p_w ^ 2 := by
  linear_combination ((1) * g73p_w ^ 2 + (-1) * g73p_w ^ 6 + (1) * g73p_w ^ 10 + (-1) * g73p_w ^ 14 + (1) * g73p_w ^ 18 + (-1) * g73p_w ^ 22 + (1) * g73p_w ^ 26) * g73p_w4

theorem g73p_p31 : g73p_w ^ 31 = -g73p_w ^ 3 := by
  linear_combination ((1) * g73p_w ^ 3 + (-1) * g73p_w ^ 7 + (1) * g73p_w ^ 11 + (-1) * g73p_w ^ 15 + (1) * g73p_w ^ 19 + (-1) * g73p_w ^ 23 + (1) * g73p_w ^ 27) * g73p_w4

theorem g73p_p32 : g73p_w ^ 32 = 1 := by
  linear_combination ((-1) * g73p_w ^ 0 + (1) * g73p_w ^ 4 + (-1) * g73p_w ^ 8 + (1) * g73p_w ^ 12 + (-1) * g73p_w ^ 16 + (1) * g73p_w ^ 20 + (-1) * g73p_w ^ 24 + (1) * g73p_w ^ 28) * g73p_w4

theorem g73p_p33 : g73p_w ^ 33 = g73p_w := by
  linear_combination ((-1) * g73p_w ^ 1 + (1) * g73p_w ^ 5 + (-1) * g73p_w ^ 9 + (1) * g73p_w ^ 13 + (-1) * g73p_w ^ 17 + (1) * g73p_w ^ 21 + (-1) * g73p_w ^ 25 + (1) * g73p_w ^ 29) * g73p_w4

theorem g73p_p34 : g73p_w ^ 34 = g73p_w ^ 2 := by
  linear_combination ((-1) * g73p_w ^ 2 + (1) * g73p_w ^ 6 + (-1) * g73p_w ^ 10 + (1) * g73p_w ^ 14 + (-1) * g73p_w ^ 18 + (1) * g73p_w ^ 22 + (-1) * g73p_w ^ 26 + (1) * g73p_w ^ 30) * g73p_w4

theorem g73p_p35 : g73p_w ^ 35 = g73p_w ^ 3 := by
  linear_combination ((-1) * g73p_w ^ 3 + (1) * g73p_w ^ 7 + (-1) * g73p_w ^ 11 + (1) * g73p_w ^ 15 + (-1) * g73p_w ^ 19 + (1) * g73p_w ^ 23 + (-1) * g73p_w ^ 27 + (1) * g73p_w ^ 31) * g73p_w4

theorem g73p_p36 : g73p_w ^ 36 = -1 := by
  linear_combination ((1) * g73p_w ^ 0 + (-1) * g73p_w ^ 4 + (1) * g73p_w ^ 8 + (-1) * g73p_w ^ 12 + (1) * g73p_w ^ 16 + (-1) * g73p_w ^ 20 + (1) * g73p_w ^ 24 + (-1) * g73p_w ^ 28 + (1) * g73p_w ^ 32) * g73p_w4

theorem g73p_p37 : g73p_w ^ 37 = -g73p_w := by
  linear_combination ((1) * g73p_w ^ 1 + (-1) * g73p_w ^ 5 + (1) * g73p_w ^ 9 + (-1) * g73p_w ^ 13 + (1) * g73p_w ^ 17 + (-1) * g73p_w ^ 21 + (1) * g73p_w ^ 25 + (-1) * g73p_w ^ 29 + (1) * g73p_w ^ 33) * g73p_w4

theorem g73p_p38 : g73p_w ^ 38 = -g73p_w ^ 2 := by
  linear_combination ((1) * g73p_w ^ 2 + (-1) * g73p_w ^ 6 + (1) * g73p_w ^ 10 + (-1) * g73p_w ^ 14 + (1) * g73p_w ^ 18 + (-1) * g73p_w ^ 22 + (1) * g73p_w ^ 26 + (-1) * g73p_w ^ 30 + (1) * g73p_w ^ 34) * g73p_w4

theorem g73p_p39 : g73p_w ^ 39 = -g73p_w ^ 3 := by
  linear_combination ((1) * g73p_w ^ 3 + (-1) * g73p_w ^ 7 + (1) * g73p_w ^ 11 + (-1) * g73p_w ^ 15 + (1) * g73p_w ^ 19 + (-1) * g73p_w ^ 23 + (1) * g73p_w ^ 27 + (-1) * g73p_w ^ 31 + (1) * g73p_w ^ 35) * g73p_w4

theorem g73p_p40 : g73p_w ^ 40 = 1 := by
  linear_combination ((-1) * g73p_w ^ 0 + (1) * g73p_w ^ 4 + (-1) * g73p_w ^ 8 + (1) * g73p_w ^ 12 + (-1) * g73p_w ^ 16 + (1) * g73p_w ^ 20 + (-1) * g73p_w ^ 24 + (1) * g73p_w ^ 28 + (-1) * g73p_w ^ 32 + (1) * g73p_w ^ 36) * g73p_w4

set_option linter.unusedSimpArgs false

theorem g73p_wp (n : ℕ) : g73p_w ^ (n + 4) = - g73p_w ^ n := by
  rw [pow_add, g73p_w4]; ring

theorem g73p_H : QAlgorithms.hadamard = g73p_m ((g73p_w - g73p_w ^ 3) / 2) ((g73p_w - g73p_w ^ 3) / 2)
    ((g73p_w - g73p_w ^ 3) / 2) (-((g73p_w - g73p_w ^ 3) / 2)) := by
  ext i j; cases i <;> cases j <;> simp [QAlgorithms.hadamard, g73p_m, ← g73p_r]

theorem g73p_T : QAlgorithms.gateT = g73p_m 1 0 0 g73p_w := by
  ext i j; cases i <;> cases j <;> simp [QAlgorithms.gateT, g73p_m, g73p_w]

theorem g73p_S : QAlgorithms.phaseS = g73p_m 1 0 0 (g73p_w ^ 2) := by
  ext i j; cases i <;> cases j <;> simp [QAlgorithms.phaseS, g73p_m, g73p_w2]

theorem g73p_Om : scalarOmega = g73p_m g73p_w 0 0 g73p_w := by
  ext i j; cases i <;> cases j <;> simp [scalarOmega, g73p_m, g73p_w]

theorem g73p_X : QAlgorithms.pauliX = g73p_m 0 1 1 0 := by
  ext i j; cases i <;> cases j <;> simp [QAlgorithms.pauliX, g73p_m]

theorem g73p_Y : QAlgorithms.pauliY = g73p_m 0 (-g73p_w ^ 2) (g73p_w ^ 2) 0 := by
  ext i j; cases i <;> cases j <;> simp [QAlgorithms.pauliY, g73p_m, g73p_w2]

theorem g73p_Z : QAlgorithms.pauliZ = g73p_m 1 0 0 (-1) := by
  ext i j; cases i <;> cases j <;> simp [QAlgorithms.pauliZ, g73p_m]

theorem g73p_one : (1 : Mat) = g73p_m 1 0 0 1 := by
  ext i j; cases i <;> cases j <;> simp [g73p_m]

theorem g73p_wstar : star g73p_w = - g73p_w ^ 3 := by
  have h3 : g73p_w ^ 3 = g73p_w * Complex.I := by rw [← g73p_w2]; ring
  rw [h3, g73p_w_eq]; apply Complex.ext <;> simp

theorem g73p_E : cliffordE.val = g73p_m ((g73p_w ^ 2 - 1) / 2) ((g73p_w ^ 2 + 1) / 2)
    ((g73p_w ^ 2 - 1) / 2) (-(g73p_w ^ 2 + 1) / 2) := by
  simp only [cliffordE, cliffordOfWord, cliffordWordMatrix, List.replicate, List.cons_append,
    List.nil_append, List.map, List.prod_cons, List.prod_nil, cliffordLetterMatrix,
    g73p_H, g73p_S, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf


theorem g73p_irr (x y : ℤ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have : Real.sqrt 2 = ((-x / y : ℚ) : ℝ) := by
      push_cast; field_simp; linarith
    exact irrational_sqrt_two ⟨_, this.symm⟩

theorem g73p_col (U : RealMat) (hU : SpecialOrthogonal U)
    (k : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsk : Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = (2 : ℝ) ^ k := by
    rw [← mul_pow, ← sq, hs2]
  have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
  intro j l
  have key : (∑ i, U i j * U i l) = if j = l then 1 else 0 := by
    have := congrFun (congrFun hU.1 j) l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have e : ∀ i, U i j * U i l = (((A i j * A i l + 2 * (B i j * B i l) : ℤ) : ℝ) +
      ((A i j * B i l + B i j * A i l : ℤ) : ℝ) * Real.sqrt 2) / 2 ^ k := by
    intro i
    rw [hcoeff, hcoeff, div_mul_div_comm, hsk]
    congr 1
    push_cast
    linear_combination ((B i j : ℝ) * B i l) * hs2
  have hsum : (∑ i, U i j * U i l) =
      ((((∑ i, (A i j * A i l + 2 * (B i j * B i l))) : ℤ) : ℝ) +
        (((∑ i, (A i j * B i l + B i j * A i l)) : ℤ) : ℝ) * Real.sqrt 2) / 2 ^ k := by
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_div]
    congr 1
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [key] at hsum
  have h3 : ((((∑ i, (A i j * A i l + 2 * (B i j * B i l))) - 2 ^ k * (if j = l then 1 else 0) : ℤ) : ℝ) +
        (((∑ i, (A i j * B i l + B i j * A i l)) : ℤ) : ℝ) * Real.sqrt 2) = 0 := by
    have := hsum
    field_simp at this
    push_cast at this ⊢
    split_ifs at this ⊢ <;> linarith
  obtain ⟨h4, h5⟩ := g73p_irr _ _ h3
  exact ⟨h5, by linarith⟩

theorem g73p_colfull (U : RealMat) (hU : SpecialOrthogonal U)
    (k : ℕ) (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hcoeff : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) :
    (∀ j l,
      (∑ i, (A i j * B i l + B i j * A i l)) = 0 ∧
      (∑ i, (A i j * A i l + 2 * (B i j * B i l))) =
        (2 : ℤ) ^ k * (if j = l then 1 else 0)) ∧
    (∀ j, (∑ i, A i j * B i j) = 0 ∧
      (∑ i, (A i j ^ 2 + 2 * B i j ^ 2)) = (2 : ℤ) ^ k) := by
  have H := g73p_col U hU k A B hcoeff
  refine ⟨H, fun j => ?_⟩
  obtain ⟨h1, h2⟩ := H j j
  constructor
  · have : (∑ i, (A i j * B i j + B i j * A i j)) = 2 * ∑ i, A i j * B i j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    omega
  · simp only [if_true, mul_one] at h2
    rw [← h2]; exact Finset.sum_congr rfl (fun i _ => by ring)


theorem g73p_val_eq (a : Fin 4 → ℤ) : omegaCoordinatesValue a =
    (((a 3 : ℝ) + ((a 2 : ℝ) - a 0) * (Real.sqrt 2 / 2) : ℝ) : ℂ) +
    (((a 1 : ℝ) + ((a 2 : ℝ) + a 0) * (Real.sqrt 2 / 2) : ℝ) : ℂ) * Complex.I := by
  have hw : QAlgorithms.gateT true true = g73p_w := rfl
  simp only [omegaCoordinatesValue, hw]
  have h2 : g73p_w ^ 2 = Complex.I := g73p_w2
  have h3 : g73p_w ^ 3 = g73p_w * Complex.I := by rw [← g73p_w2]; ring
  rw [h3, h2, g73p_w_eq]
  push_cast
  linear_combination ((a 0 : ℂ) * ((Real.sqrt 2 : ℂ) / 2)) * Complex.I_sq

theorem g73p_normSq (a : Fin 4 → ℤ) : Complex.normSq (omegaCoordinatesValue a) =
    ((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 : ℤ) : ℝ) +
    ((a 3 * (a 2 - a 0) + a 1 * (a 2 + a 0) : ℤ) : ℝ) * Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [g73p_val_eq, Complex.normSq_add_mul_I]
  push_cast
  linear_combination ((((a 2 : ℝ) - a 0) ^ 2 + ((a 2 : ℝ) + a 0) ^ 2) / 4) * hs2

theorem g73p_sq4 (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero h
    rw [h, hm, show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; simp
  · have hm : x = 2 * (x / 2) + 1 := by omega
    rw [h, hm, show (2 * (x / 2) + 1) ^ 2 = 1 + 4 * ((x / 2) ^ 2 + x / 2) by ring,
      Int.add_mul_emod_self_left]; rfl

theorem g73p_par (x : ℤ) : ((x : ZMod 2) = 0 → x % 2 = 0) ∧ ((x : ZMod 2) = 1 → x % 2 = 1) := by
  constructor
  · intro h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).1 h
    omega
  · intro h
    have h' : ((x : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by simpa using h
    have := (ZMod.intCast_eq_intCast_iff' x 1 2).1 h'
    simpa using this

theorem g73p_res4 (u : ℂ) (hu : InZomega u)
    (hru : residue u = bits 1 ∨ residue u = bits 2 ∨ residue u = bits 4 ∨ residue u = bits 8) :
    ∃ a : Fin 4 → ℤ, omegaCoordinatesValue a = u ∧ (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) % 4 = 1 := by
  have hc : omegaCoordinatesValue (omegaCoordinates u) = u := by
    simp only [omegaCoordinates, dif_pos hu]; exact Classical.choose_spec hu
  refine ⟨omegaCoordinates u, hc, ?_⟩
  set a := omegaCoordinates u
  have e : ∀ n, residue u = bits n → ∀ i, (a i : ZMod 2) = bits n i := by
    intro n h i; rw [← h]; rfl
  have q0 := g73p_sq4 (a 0); have q1 := g73p_sq4 (a 1)
  have q2 := g73p_sq4 (a 2); have q3 := g73p_sq4 (a 3)
  have p0 := g73p_par (a 0); have p1 := g73p_par (a 1)
  have p2 := g73p_par (a 2); have p3 := g73p_par (a 3)
  generalize a 0 ^ 2 = s0 at *
  generalize a 1 ^ 2 = s1 at *
  generalize a 2 ^ 2 = s2 at *
  generalize a 3 ^ 2 = s3 at *
  rcases hru with h | h | h | h <;> have b := e _ h <;>
    have b0 := b 0 <;> have b1 := b 1 <;> have b2 := b 2 <;> have b3 := b 3 <;>
    simp [bits] at b0 b1 b2 b3 <;>
    have c0 := p0.1 <;> have d0 := p0.2 <;> have c1 := p1.1 <;> have d1 := p1.2 <;>
    have c2 := p2.1 <;> have d2 := p2.2 <;> have c3 := p3.1 <;> have d3 := p3.2 <;>
    simp_all <;> omega

theorem g73p_forb (k : ℕ) (hk : 2 ≤ k)
    (u t : ℂ) (hu : InZomega u) (ht : InZomega t)
    (hru : residue u = bits 1 ∨ residue u = bits 2 ∨ residue u = bits 4 ∨ residue u = bits 8)
    (hrt : residue t = bits 1 ∨ residue t = bits 2 ∨ residue t = bits 4 ∨ residue t = bits 8) :
    Complex.normSq (u / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) +
      Complex.normSq (t / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) ≠ 1 := by
  obtain ⟨a, rfl, ha⟩ := g73p_res4 u hu hru
  obtain ⟨b, rfl, hb⟩ := g73p_res4 t ht hrt
  intro h
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ) ^ k) = 2 ^ k := by
    rw [map_pow, Complex.normSq_ofReal, ← sq, hs2]
  rw [Complex.normSq_div, Complex.normSq_div, hn, g73p_normSq, g73p_normSq] at h
  have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp at h
  have h3 : (((a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2) + (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2) - 2 ^ k : ℤ) : ℝ) +
      (((a 3 * (a 2 - a 0) + a 1 * (a 2 + a 0)) + (b 3 * (b 2 - b 0) + b 1 * (b 2 + b 0)) : ℤ) : ℝ) *
        Real.sqrt 2 = 0 := by
    push_cast at h ⊢; linarith
  have h4 := (g73p_irr _ _ h3).1
  have h5 : (2 : ℤ) ^ k % 4 = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add]; norm_num
  omega


theorem g73p_ocv (a : Fin 4 → ℤ) : omegaCoordinatesValue a =
    (a 0 : ℂ) * g73p_w ^ 3 + (a 1 : ℂ) * g73p_w ^ 2 + (a 2 : ℂ) * g73p_w + (a 3 : ℂ) := rfl

theorem g73p_zadd {x y : ℂ} (hx : InZomega x) (hy : InZomega y) : InZomega (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  refine ⟨a + b, ?_⟩; simp only [g73p_ocv, Pi.add_apply]; push_cast; ring

theorem g73p_zneg {x : ℂ} (hx : InZomega x) : InZomega (-x) := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨-a, ?_⟩; simp only [g73p_ocv, Pi.neg_apply]; push_cast; ring

theorem g73p_zmul {x y : ℂ} (hx : InZomega x) (hy : InZomega y) : InZomega (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  refine ⟨![a 3 * b 0 + a 2 * b 1 + a 1 * b 2 + a 0 * b 3,
    a 3 * b 1 + a 2 * b 2 + a 1 * b 3 - a 0 * b 0,
    a 3 * b 2 + a 2 * b 3 - (a 1 * b 0 + a 0 * b 1),
    a 3 * b 3 - (a 2 * b 0 + a 1 * b 1 + a 0 * b 2)], ?_⟩
  simp only [g73p_ocv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring_nf
  try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]
  ring_nf

theorem g73p_zint (n : ℤ) : InZomega (n : ℂ) := ⟨![0, 0, 0, n], by
  simp [g73p_ocv]⟩

theorem g73p_zw : InZomega g73p_w := ⟨![0, 0, 1, 0], by simp [g73p_ocv]⟩

theorem g73p_zI : InZomega Complex.I := ⟨![0, 1, 0, 0], by simp [g73p_ocv, g73p_w2]⟩

theorem g73p_zstar {x : ℂ} (hx : InZomega x) : InZomega (star x) := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨![-a 2, -a 1, -a 0, a 3], ?_⟩
  simp only [g73p_ocv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, star_add, star_mul', star_pow,
    star_intCast, g73p_wstar]
  push_cast
  ring_nf
  try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]
  ring_nf

theorem g73p_dz {x : ℂ} (hx : InZomega x) : InDomega x := ⟨0, by simpa using hx⟩

theorem g73p_d2 (k : ℕ) : InZomega ((2 : ℂ) ^ k) := by
  have := g73p_zint (2 ^ k); push_cast at this; exact this

theorem g73p_dadd {x y : ℂ} (hx : InDomega x) (hy : InDomega y) : InDomega (x + y) := by
  obtain ⟨k, hk⟩ := hx; obtain ⟨l, hl⟩ := hy
  refine ⟨k + l, ?_⟩
  have : (2 : ℂ) ^ (k + l) * (x + y) = (2 : ℂ) ^ l * ((2 : ℂ) ^ k * x) + (2 : ℂ) ^ k * ((2 : ℂ) ^ l * y) := by
    ring
  rw [this]; exact g73p_zadd (g73p_zmul (g73p_d2 l) hk) (g73p_zmul (g73p_d2 k) hl)

theorem g73p_dmul {x y : ℂ} (hx : InDomega x) (hy : InDomega y) : InDomega (x * y) := by
  obtain ⟨k, hk⟩ := hx; obtain ⟨l, hl⟩ := hy
  refine ⟨k + l, ?_⟩
  have : (2 : ℂ) ^ (k + l) * (x * y) = ((2 : ℂ) ^ k * x) * ((2 : ℂ) ^ l * y) := by ring
  rw [this]; exact g73p_zmul hk hl

theorem g73p_dstar {x : ℂ} (hx : InDomega x) : InDomega (star x) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  have := g73p_zstar hk
  simpa [star_mul', star_pow] using this

theorem g73p_dneg {x : ℂ} (hx : InDomega x) : InDomega (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [mul_neg]; exact g73p_zneg hk⟩

theorem g73p_dr : InDomega ((g73p_w - g73p_w ^ 3) / 2) := by
  refine ⟨1, ?_⟩
  have : (2 : ℂ) ^ 1 * ((g73p_w - g73p_w ^ 3) / 2) = g73p_w + -(g73p_w ^ 2 * g73p_w) := by ring
  rw [this]
  exact g73p_zadd g73p_zw (g73p_zneg (g73p_zmul (by rw [g73p_w2]; exact g73p_zI) g73p_zw))

def g73p_DM (U : Mat) : Prop := ∀ i j, InDomega (U i j)

theorem g73p_DMmul {A B : Mat} (hA : g73p_DM A) (hB : g73p_DM B) : g73p_DM (A * B) := by
  intro i j
  rw [Matrix.mul_apply, Fintype.sum_bool]
  exact g73p_dadd (g73p_dmul (hA _ _) (hB _ _)) (g73p_dmul (hA _ _) (hB _ _))

theorem g73p_DMm {a b c d : ℂ} (ha : InDomega a) (hb : InDomega b) (hc : InDomega c)
    (hd : InDomega d) : g73p_DM (g73p_m a b c d) := by
  intro i j; cases i <;> cases j <;> simpa [g73p_m]

theorem g73p_D0 : InDomega 0 := g73p_dz (by simpa using g73p_zint 0)
theorem g73p_D1 : InDomega 1 := g73p_dz (by simpa using g73p_zint 1)

theorem g73p_DMcl (w : List CliffordLetter) : g73p_DM (cliffordWordMatrix w) := by
  induction w with
  | nil => rw [show cliffordWordMatrix [] = 1 from rfl, g73p_one]
           exact g73p_DMm g73p_D1 g73p_D0 g73p_D0 g73p_D1
  | cons a w ih =>
    rw [show cliffordWordMatrix (a :: w) = cliffordLetterMatrix a * cliffordWordMatrix w from by
      simp [cliffordWordMatrix]]
    refine g73p_DMmul ?_ ih
    cases a
    · rw [show cliffordLetterMatrix .h = QAlgorithms.hadamard from rfl, g73p_H]
      exact g73p_DMm g73p_dr g73p_dr g73p_dr (g73p_dneg g73p_dr)
    · rw [show cliffordLetterMatrix .s = QAlgorithms.phaseS from rfl, g73p_S, g73p_w2]
      exact g73p_DMm g73p_D1 g73p_D0 g73p_D0 (g73p_dz g73p_zI)
    · rw [show cliffordLetterMatrix .omega = scalarOmega from rfl, g73p_Om]
      exact g73p_DMm (g73p_dz g73p_zw) g73p_D0 g73p_D0 (g73p_dz g73p_zw)

theorem g73p_DMinput (w : List Input) : g73p_DM (inputWordMatrix w) := by
  induction w with
  | nil => rw [show inputWordMatrix [] = 1 from rfl, g73p_one]
           exact g73p_DMm g73p_D1 g73p_D0 g73p_D0 g73p_D1
  | cons a w ih =>
    rw [show inputWordMatrix (a :: w) = inputMatrix a * inputWordMatrix w from by
      simp [inputWordMatrix]]
    refine g73p_DMmul ?_ ih
    cases a with
    | clifford C =>
      obtain ⟨U, v, hv⟩ := C
      show g73p_DM U
      rw [← hv]; exact g73p_DMcl v
    | t =>
      show g73p_DM QAlgorithms.gateT
      rw [g73p_T]; exact g73p_DMm g73p_D1 g73p_D0 g73p_D0 (g73p_dz g73p_zw)

theorem g73p_re (z : ℂ) (hz : InDomega z) : InDsqrt2 (z.re / 2) := by
  obtain ⟨k, a, ha⟩ := hz
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hre : (2 : ℝ) ^ k * z.re = (a 3 : ℝ) + ((a 2 : ℝ) - a 0) * (Real.sqrt 2 / 2) := by
    have h2 : ((2 : ℂ) ^ k) = (((2 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; ring
    have := congrArg Complex.re ha
    rw [h2, Complex.re_ofReal_mul, g73p_val_eq] at this
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at this
    linarith
  refine ⟨2 * k + 3, a 2 - a 0, a 3, ?_⟩
  have : Real.sqrt 2 ^ (2 * k + 3) = 2 * Real.sqrt 2 * (2 : ℝ) ^ k := by
    rw [pow_add, pow_mul, hs2, show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hs2]; ring
  rw [this]
  push_cast
  have e : 2 * Real.sqrt 2 * 2 ^ k * (z.re / 2) = Real.sqrt 2 * ((2 : ℝ) ^ k * z.re) := by ring
  rw [e, hre]
  linear_combination ((a 2 : ℝ) - a 0) / 2 * hs2

theorem g73p_DMsigma (i : Fin 3) : g73p_DM (sigma i) := by
  fin_cases i
  · show g73p_DM QAlgorithms.pauliX
    rw [g73p_X]; exact g73p_DMm g73p_D0 g73p_D1 g73p_D1 g73p_D0
  · show g73p_DM QAlgorithms.pauliY
    rw [g73p_Y, g73p_w2]
    exact g73p_DMm g73p_D0 (g73p_dneg (g73p_dz g73p_zI)) (g73p_dz g73p_zI) g73p_D0
  · show g73p_DM QAlgorithms.pauliZ
    rw [g73p_Z]; exact g73p_DMm g73p_D1 g73p_D0 g73p_D0 (g73p_dneg g73p_D1)

theorem g73p_entry (U : Mat) (hU : CliffordT U) :
    (∀ i j, InDomega (U i j)) ∧ (∀ i j, InDsqrt2 (operatorBloch U i j)) := by
  obtain ⟨w, rfl⟩ := hU
  have h1 := g73p_DMinput w
  refine ⟨h1, fun i j => ?_⟩
  have hs : g73p_DM (star (inputWordMatrix w)) := by
    intro a b; rw [Matrix.star_apply]; exact g73p_dstar (h1 _ _)
  have hp := g73p_DMmul (g73p_DMmul (g73p_DMmul (g73p_DMsigma i) h1) (g73p_DMsigma j)) hs
  apply g73p_re
  rw [Matrix.trace, Fintype.sum_bool]
  exact g73p_dadd (hp _ _) (hp _ _)


/-- Remark 4.4, PDF p.4: both entry-ring conclusions, with the actual Bloch map. -/
theorem solution (U : Mat) (hU : CliffordT U) :
    (∀ i j, InDomega (U i j)) ∧ (∀ i j, InDsqrt2 (operatorBloch U i j)) := by
  exact g73p_entry U hU


end
