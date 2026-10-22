-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.original_bs_nonunique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:49:58.683195+00:00
-- url     : https://prove2.me/submissions/3a044499-31eb-4e77-960f-c531cfbbdb2e

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


theorem g73p_E2 : cliffordE2.val = cliffordE.val * cliffordE.val := by
  simp only [cliffordE2, cliffordE, cliffordOfWord, cliffordWordMatrix, List.map_append,
    List.prod_append]

theorem g73p_Es : star cliffordE.val = g73p_m (-(g73p_w ^ 2 + 1) / 2) (-(g73p_w ^ 2 + 1) / 2)
    (-(g73p_w ^ 2 - 1) / 2) ((g73p_w ^ 2 - 1) / 2) := by
  rw [g73p_E, g73p_m_star]
  simp only [star_div₀, star_sub, star_add, star_neg, star_pow, g73p_wstar, star_one, star_ofNat]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_e_order :
    cliffordE.val ^ 3 = 1 ∧
    cliffordE.val * QAlgorithms.pauliX * star cliffordE.val = QAlgorithms.pauliY ∧
    cliffordE.val * QAlgorithms.pauliY * star cliffordE.val = QAlgorithms.pauliZ ∧
    cliffordE.val * QAlgorithms.pauliZ * star cliffordE.val = QAlgorithms.pauliX := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_succ, pow_succ, pow_one, g73p_E, g73p_m_mul, g73p_m_mul, g73p_one]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf
  · rw [g73p_Es, g73p_E, g73p_X, g73p_Y, g73p_m_mul, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf
  · rw [g73p_Es, g73p_E, g73p_Z, g73p_Y, g73p_m_mul, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf
  · rw [g73p_Es, g73p_E, g73p_X, g73p_Z, g73p_m_mul, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_twoBS :
    twoSidedBSWitness 0 ≠ twoSidedBSWitness 1 ∧
    twoSidedBSValue (twoSidedBSWitness 0) = twoSidedBSValue (twoSidedBSWitness 1) ∧
    twoSidedBSWitness 2 ≠ twoSidedBSWitness 3 ∧
    twoSidedBSValue (twoSidedBSWitness 2) = twoSidedBSValue (twoSidedBSWitness 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun M => M.left.val) h
    simp [twoSidedBSWitness, cliffordZ, cliffordI, cliffordOfWord, cliffordWordMatrix,
      cliffordLetterMatrix] at this
    have h2 := congrFun (congrFun this true) true
    norm_num [QAlgorithms.phaseS] at h2
  · simp (config := {decide := true}) only [twoSidedBSWitness, twoSidedBSValue, cliffordZ, cliffordI, cliffordX,
      cliffordYS, cliffordXOmega, cliffordH, cliffordSH, cliffordOfWord,
      cliffordWordMatrix, List.map, List.prod_cons, List.prod_nil, cliffordLetterMatrix, Fin.val_one, Fin.val_two,
      pow_succ, pow_zero, ↓reduceIte]
    simp only [g73p_H, g73p_S, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf
  · intro h
    have := congrArg (fun M => M.left.val) h
    simp (config := {decide := true}) only [twoSidedBSWitness, cliffordYS, cliffordI, cliffordOfWord, cliffordWordMatrix,
      cliffordLetterMatrix, List.map, List.prod_cons, List.prod_nil, ↓reduceIte] at this
    simp only [g73p_H, g73p_S, g73p_Om, g73p_one, g73p_m_mul] at this
    have h2 := congrFun (congrFun this false) false
    simp only [g73p_m, Matrix.of_apply, Bool.false_eq_true, ↓reduceIte] at h2
    ring_nf at h2
    try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40] at h2
    ring_nf at h2
    norm_num at h2
  · simp (config := {decide := true}) only [twoSidedBSWitness, twoSidedBSValue, cliffordZ, cliffordI, cliffordX,
      cliffordYS, cliffordXOmega, cliffordH, cliffordSH, cliffordOfWord,
      cliffordWordMatrix, List.map, List.prod_cons, List.prod_nil, cliffordLetterMatrix, Fin.val_one, Fin.val_two,
      pow_succ, pow_zero, ↓reduceIte]
    simp only [g73p_H, g73p_S, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_origBS :
    originalBSWitness 0 ≠ originalBSWitness 1 ∧
    originalBSValue (originalBSWitness 0) = originalBSValue (originalBSWitness 1) ∧
    originalBSWitness 2 ≠ originalBSWitness 3 ∧
    originalBSValue (originalBSWitness 2) = originalBSValue (originalBSWitness 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun M => M.leadingH) h
    simp [originalBSWitness] at this
  · simp (config := {decide := true}) only [originalBSWitness, originalBSValue, cliffordZ, cliffordI, cliffordX,
      cliffordYS, cliffordXOmega, cliffordH, cliffordSH, cliffordOfWord,
      cliffordWordMatrix, List.map, List.prod_cons, List.prod_nil, cliffordLetterMatrix, Fin.val_one, Fin.val_two,
      pow_succ, pow_zero, ↓reduceIte]
    simp only [g73p_H, g73p_S, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf
  · intro h
    have := congrArg (fun M => M.leadingH) h
    simp [originalBSWitness] at this
  · simp (config := {decide := true}) only [originalBSWitness, originalBSValue, cliffordZ, cliffordI, cliffordX,
      cliffordYS, cliffordXOmega, cliffordH, cliffordSH, cliffordOfWord,
      cliffordWordMatrix, List.map, List.prod_cons, List.prod_nil, cliffordLetterMatrix, Fin.val_one, Fin.val_two,
      pow_succ, pow_zero, ↓reduceIte]
    simp only [g73p_H, g73p_S, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_axis :
    cliffordE.val * axisTGate 0 = axisTGate 1 * cliffordE.val ∧
    cliffordE.val * axisTGate 1 = axisTGate 2 * cliffordE.val ∧
    cliffordE.val * axisTGate 2 = axisTGate 0 * cliffordE.val := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp (config := {decide := true}) only [axisTGate, g73p_E2, ↓reduceIte]
    simp only [g73p_E, g73p_T, g73p_m_mul]
    apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf


/-- Section 8.3 after (21), PDF p.12: BOTH explicit pairs of distinct original
BS forms with identical operators: H.H = I and SHTH.Z = H.SHTH. -/
theorem solution :
    originalBSWitness 0 ≠ originalBSWitness 1 ∧
    originalBSValue (originalBSWitness 0) = originalBSValue (originalBSWitness 1) ∧
    originalBSWitness 2 ≠ originalBSWitness 3 ∧
    originalBSValue (originalBSWitness 2) = originalBSValue (originalBSWitness 3) := by
  exact g73p_origBS


end
