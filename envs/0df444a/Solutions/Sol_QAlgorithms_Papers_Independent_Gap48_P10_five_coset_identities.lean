-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.five_coset_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:17:53.341347+00:00
-- url     : https://prove2.me/submissions/b188570c-69dd-459c-815b-c7c5751cf1af

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


theorem g73p_wdef : QAlgorithms.gateT true true = g73p_w := rfl

theorem g73p_cyc (t : ℂ) (ht : InZomega t) :
    ∃ q : ℂ, InZomega q ∧ t + star t = ((Real.sqrt 2 : ℝ) : ℂ) * q := by
  obtain ⟨a, rfl⟩ := ht
  refine ⟨omegaCoordinatesValue ![-a 3, 0, a 3, a 2 - a 0], ⟨_, rfl⟩, ?_⟩
  simp only [omegaCoordinatesValue, g73p_wdef, star_add, star_mul', star_pow, star_intCast,
    g73p_wstar, g73p_sqrt2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring_nf
  try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]
  ring_nf


theorem g73p_sm (w : List SmallLetter) : (w.map smallLetterMatrix).prod ∈ smallSet := ⟨w, rfl⟩

theorem g73p_smul {a b : Mat} (ha : a ∈ smallSet) (hb : b ∈ smallSet) : a * b ∈ smallSet := by
  obtain ⟨u, rfl⟩ := ha; obtain ⟨v, rfl⟩ := hb
  exact ⟨u ++ v, by simp [List.prod_append]⟩

theorem g73p_s1 : (1 : Mat) ∈ smallSet := ⟨[], rfl⟩

theorem g73p_cmul {a b : Mat} (ha : a ∈ cliffordSet) (hb : b ∈ cliffordSet) : a * b ∈ cliffordSet := by
  obtain ⟨u, rfl⟩ := ha; obtain ⟨v, rfl⟩ := hb
  exact ⟨u ++ v, by simp [cliffordWordMatrix, List.prod_append]⟩

theorem g73p_cH : QAlgorithms.hadamard ∈ cliffordSet := ⟨[.h], by simp [cliffordWordMatrix, cliffordLetterMatrix]⟩
theorem g73p_cS : QAlgorithms.phaseS ∈ cliffordSet := ⟨[.s], by simp [cliffordWordMatrix, cliffordLetterMatrix]⟩
theorem g73p_cO : scalarOmega ∈ cliffordSet := ⟨[.omega], by simp [cliffordWordMatrix, cliffordLetterMatrix]⟩
theorem g73p_c1 : (1 : Mat) ∈ cliffordSet := ⟨[], rfl⟩

theorem g73p_iX : QAlgorithms.pauliX = QAlgorithms.hadamard * QAlgorithms.phaseS * QAlgorithms.phaseS * QAlgorithms.hadamard := by
  simp only [g73p_H, g73p_S, g73p_X, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_cX : QAlgorithms.pauliX ∈ cliffordSet := by
  rw [g73p_iX]; exact g73p_cmul (g73p_cmul (g73p_cmul g73p_cH g73p_cS) g73p_cS) g73p_cH

theorem g73p_scw (w : List SmallLetter) : (w.map smallLetterMatrix).prod ∈ cliffordSet := by
  induction w with
  | nil => exact g73p_c1
  | cons g w ih =>
    rw [List.map_cons, List.prod_cons]
    refine g73p_cmul ?_ ih
    cases g
    · exact g73p_cS
    · exact g73p_cX
    · exact g73p_cO

theorem g73p_sc {a : Mat} (ha : a ∈ smallSet) : a ∈ cliffordSet := by
  obtain ⟨w, rfl⟩ := ha; exact g73p_scw w

theorem g73p_i2 : QAlgorithms.phaseS * (QAlgorithms.phaseS * QAlgorithms.hadamard) = QAlgorithms.hadamard * ([.x].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_i3 : QAlgorithms.pauliX * QAlgorithms.hadamard = QAlgorithms.hadamard * ([.s, .s].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_i4 : QAlgorithms.pauliX * (QAlgorithms.phaseS * QAlgorithms.hadamard) = (QAlgorithms.phaseS * QAlgorithms.hadamard) * ([.omega, .omega, .x, .s, .s].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_i5 : scalarOmega * QAlgorithms.hadamard = QAlgorithms.hadamard * ([.omega].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_i6 : scalarOmega * (QAlgorithms.phaseS * QAlgorithms.hadamard) = (QAlgorithms.phaseS * QAlgorithms.hadamard) * ([.omega].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_i7 : QAlgorithms.hadamard * QAlgorithms.hadamard = 1 := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_i8 : QAlgorithms.hadamard * (QAlgorithms.phaseS * QAlgorithms.hadamard) = (QAlgorithms.phaseS * QAlgorithms.hadamard) * ([.omega, .x, .s, .s, .s].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_t1 : QAlgorithms.phaseS * QAlgorithms.gateT = QAlgorithms.gateT * QAlgorithms.phaseS := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_t2 : scalarOmega * QAlgorithms.gateT = QAlgorithms.gateT * scalarOmega := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_t3 : QAlgorithms.pauliX * QAlgorithms.gateT = QAlgorithms.gateT * ([.omega, .omega, .omega, .omega, .omega, .omega, .omega, .x, .s].map smallLetterMatrix).prod := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_t4 : QAlgorithms.gateT * QAlgorithms.pauliX = ([.omega, .x, .s, .s, .s].map smallLetterMatrix).prod * QAlgorithms.gateT := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_t5 : QAlgorithms.gateT * QAlgorithms.gateT = QAlgorithms.phaseS := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf

theorem g73p_t6 : QAlgorithms.gateT * ([.s, .s, .s].map smallLetterMatrix).prod * QAlgorithms.gateT = 1 := by
  simp only [List.map, List.prod_cons, List.prod_nil, smallLetterMatrix, g73p_H, g73p_S, g73p_X, g73p_T, g73p_Om, g73p_one, g73p_m_mul]
  apply g73p_m_ext <;> (ring_nf <;> try simp only [g73p_p4, g73p_p5, g73p_p6, g73p_p7, g73p_p8, g73p_p9, g73p_p10, g73p_p11, g73p_p12, g73p_p13, g73p_p14, g73p_p15, g73p_p16, g73p_p17, g73p_p18, g73p_p19, g73p_p20, g73p_p21, g73p_p22, g73p_p23, g73p_p24, g73p_p25, g73p_p26, g73p_p27, g73p_p28, g73p_p29, g73p_p30, g73p_p31, g73p_p32, g73p_p33, g73p_p34, g73p_p35, g73p_p36, g73p_p37, g73p_p38, g73p_p39, g73p_p40]) <;> try ring_nf


theorem g73p_step {g t t' u s : Mat} (h : g * t = t' * u) : t' * (u * s) = g * (t * s) := by
  rw [← mul_assoc, ← h, mul_assoc]

theorem g73p_part1 : cliffordSet = transversal * smallSet := by
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    induction w with
    | nil => exact Set.mem_mul.2 ⟨1, by simp [transversal], 1, g73p_s1, by simp [cliffordWordMatrix]⟩
    | cons g w ih =>
      obtain ⟨t, ht, s, hs, hts⟩ := Set.mem_mul.1 ih
      rw [show cliffordWordMatrix (g :: w) = cliffordLetterMatrix g * cliffordWordMatrix w from by
        simp [cliffordWordMatrix], ← hts]
      simp only [transversal, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rw [Set.mem_mul]
      cases g <;> rcases ht with rfl | rfl | rfl <;> simp only [cliffordLetterMatrix]
      · exact ⟨QAlgorithms.hadamard, by simp [transversal], _ * s, g73p_smul (g73p_sm []) hs, g73p_step (by simp)⟩
      · exact ⟨1, by simp [transversal], _ * s, g73p_smul (g73p_sm []) hs, g73p_step (by simp [g73p_i7])⟩
      · exact ⟨(QAlgorithms.phaseS * QAlgorithms.hadamard), by simp [transversal], _ * s, g73p_smul (g73p_sm [.omega, .x, .s, .s, .s]) hs, g73p_step (g73p_i8)⟩
      · exact ⟨1, by simp [transversal], _ * s, g73p_smul (g73p_sm [.s]) hs, g73p_step (by simp [smallLetterMatrix])⟩
      · exact ⟨(QAlgorithms.phaseS * QAlgorithms.hadamard), by simp [transversal], _ * s, g73p_smul (g73p_sm []) hs, g73p_step (by simp)⟩
      · exact ⟨QAlgorithms.hadamard, by simp [transversal], _ * s, g73p_smul (g73p_sm [.x]) hs, g73p_step (g73p_i2)⟩
      · exact ⟨1, by simp [transversal], _ * s, g73p_smul (g73p_sm [.omega]) hs, g73p_step (by simp [smallLetterMatrix])⟩
      · exact ⟨QAlgorithms.hadamard, by simp [transversal], _ * s, g73p_smul (g73p_sm [.omega]) hs, g73p_step (g73p_i5)⟩
      · exact ⟨(QAlgorithms.phaseS * QAlgorithms.hadamard), by simp [transversal], _ * s, g73p_smul (g73p_sm [.omega]) hs, g73p_step (g73p_i6)⟩
  · rintro _ ⟨t, ht, s, hs, rfl⟩
    refine g73p_cmul ?_ (g73p_sc hs)
    simp only [transversal, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact g73p_c1
    · exact g73p_cH
    · exact g73p_cmul g73p_cS g73p_cH

def g73p_Mono (M : Mat) : Prop :=
  (M false true = 0 ∧ M true false = 0 ∧ M false false ≠ 0 ∧ M true true ≠ 0) ∨
  (M false false = 0 ∧ M true true = 0 ∧ M false true ≠ 0 ∧ M true false ≠ 0)

theorem g73p_wne : g73p_w ≠ 0 := by
  intro h; have := g73p_w4; rw [h] at this; norm_num at this

theorem g73p_monow (w : List SmallLetter) : g73p_Mono (w.map smallLetterMatrix).prod := by
  induction w with
  | nil => left; simp
  | cons g w ih =>
    rw [List.map_cons, List.prod_cons]
    unfold g73p_Mono at ih ⊢
    cases g <;> simp only [smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega,
      Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply] <;> simp [g73p_wdef, g73p_wne, Complex.I_ne_zero] <;> tauto

theorem g73p_notsmall (h s : Mat) (hh : h ∈ nonidentityTransversal) (hs : s ∈ smallSet) :
    h * s ∉ smallSet := by
  intro hm
  obtain ⟨w, rfl⟩ := hs
  obtain ⟨v, hv⟩ := hm
  have m1 := g73p_monow w
  have m2 := g73p_monow v
  have hv' : (v.map smallLetterMatrix).prod = h * (w.map smallLetterMatrix).prod := hv
  rw [hv'] at m2
  have hr : ∃ r : ℂ, r ≠ 0 ∧ h false false = r ∧ h false true = r := by
    simp only [nonidentityTransversal, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    refine ⟨(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), by simp, ?_⟩
    rcases hh with rfl | rfl <;>
      simp [QAlgorithms.hadamard, QAlgorithms.phaseS, Matrix.mul_apply, Fintype.sum_bool]
  obtain ⟨r, hr0, h1, h2⟩ := hr
  unfold g73p_Mono at m1 m2
  simp only [Matrix.mul_apply, Fintype.sum_bool, h1, h2] at m2
  rcases m1 with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ <;>
    rcases m2 with ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3, b4⟩ <;> simp_all

theorem g73p_part2 : cliffordSet \ smallSet = nonidentityTransversal * smallSet := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxs⟩
    rw [g73p_part1] at hx
    obtain ⟨t, ht, s, hs, rfl⟩ := hx
    simp only [transversal, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd (by simpa using hs) hxs
    · exact ⟨_, by simp [nonidentityTransversal], s, hs, rfl⟩
    · exact ⟨_, by simp [nonidentityTransversal], s, hs, rfl⟩
  · rintro x ⟨h, hh, s, hs, rfl⟩
    refine ⟨?_, g73p_notsmall h s hh hs⟩
    rw [g73p_part1]
    refine ⟨h, ?_, s, hs, rfl⟩
    simp only [nonidentityTransversal, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    simp only [transversal, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

theorem g73p_part3 : smallSet * nonidentityTransversal ⊆ nonidentityTransversal * smallSet := by
  rintro _ ⟨s, hs, h, hh, rfl⟩
  obtain ⟨w, rfl⟩ := hs
  induction w generalizing h with
  | nil => exact ⟨h, hh, 1, g73p_s1, by simp⟩
  | cons g w ih =>
    obtain ⟨h', hh', s', hs', he⟩ := ih h hh
    have he' : h' * s' = (w.map smallLetterMatrix).prod * h := he
    show (List.map smallLetterMatrix (g :: w)).prod * h ∈ _
    rw [List.map_cons, List.prod_cons, mul_assoc, ← he']
    simp only [nonidentityTransversal, Set.mem_insert_iff, Set.mem_singleton_iff] at hh'
    rw [Set.mem_mul]
    cases g <;> rcases hh' with rfl | rfl <;> simp only [smallLetterMatrix]
    · exact ⟨(QAlgorithms.phaseS * QAlgorithms.hadamard), by simp [nonidentityTransversal], _ * s', g73p_smul (g73p_sm []) hs', g73p_step (by simp)⟩
    · exact ⟨QAlgorithms.hadamard, by simp [nonidentityTransversal], _ * s', g73p_smul (g73p_sm [.x]) hs', g73p_step (g73p_i2)⟩
    · exact ⟨QAlgorithms.hadamard, by simp [nonidentityTransversal], _ * s', g73p_smul (g73p_sm [.s, .s]) hs', g73p_step (g73p_i3)⟩
    · exact ⟨(QAlgorithms.phaseS * QAlgorithms.hadamard), by simp [nonidentityTransversal], _ * s', g73p_smul (g73p_sm [.omega, .omega, .x, .s, .s]) hs', g73p_step (g73p_i4)⟩
    · exact ⟨QAlgorithms.hadamard, by simp [nonidentityTransversal], _ * s', g73p_smul (g73p_sm [.omega]) hs', g73p_step (g73p_i5)⟩
    · exact ⟨(QAlgorithms.phaseS * QAlgorithms.hadamard), by simp [nonidentityTransversal], _ * s', g73p_smul (g73p_sm [.omega]) hs', g73p_step (g73p_i6)⟩

theorem g73p_rT (w : List SmallLetter) : ∃ s ∈ smallSet,
    (w.map smallLetterMatrix).prod * QAlgorithms.gateT = QAlgorithms.gateT * s := by
  induction w with
  | nil => exact ⟨1, g73p_s1, by simp⟩
  | cons g w ih =>
    obtain ⟨s, hs, he⟩ := ih
    rw [List.map_cons, List.prod_cons, mul_assoc, he, ← mul_assoc]
    cases g <;> simp only [smallLetterMatrix]
    · exact ⟨_, g73p_smul (g73p_sm [.s]) hs, by rw [g73p_t1, mul_assoc]; simp [smallLetterMatrix]⟩
    · exact ⟨_, g73p_smul (g73p_sm _) hs, by rw [g73p_t3, mul_assoc]⟩
    · exact ⟨_, g73p_smul (g73p_sm [.omega]) hs, by rw [g73p_t2, mul_assoc]; simp [smallLetterMatrix]⟩

theorem g73p_lT (w : List SmallLetter) : ∃ s ∈ smallSet,
    QAlgorithms.gateT * (w.map smallLetterMatrix).prod = s * QAlgorithms.gateT := by
  induction w with
  | nil => exact ⟨1, g73p_s1, by simp⟩
  | cons g w ih =>
    obtain ⟨s, hs, he⟩ := ih
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    cases g <;> simp only [smallLetterMatrix]
    · exact ⟨_, g73p_smul (g73p_sm [.s]) hs, by
        rw [← g73p_t1, mul_assoc, he, ← mul_assoc]; simp [smallLetterMatrix]⟩
    · exact ⟨_, g73p_smul (g73p_sm _) hs, by rw [g73p_t4, mul_assoc, he, ← mul_assoc]⟩
    · exact ⟨_, g73p_smul (g73p_sm [.omega]) hs, by
        rw [← g73p_t2, mul_assoc, he, ← mul_assoc]; simp [smallLetterMatrix]⟩

theorem g73p_part4 : smallSet * {QAlgorithms.gateT} = {QAlgorithms.gateT} * smallSet := by
  rw [Set.mul_singleton, Set.singleton_mul]
  apply Set.Subset.antisymm
  · rintro _ ⟨s, ⟨w, rfl⟩, rfl⟩
    obtain ⟨s', hs', he⟩ := g73p_rT w
    exact ⟨s', hs', he.symm⟩
  · rintro _ ⟨s, ⟨w, rfl⟩, rfl⟩
    obtain ⟨s', hs', he⟩ := g73p_lT w
    exact ⟨s', hs', he.symm⟩

theorem g73p_part5 : ({QAlgorithms.gateT} * smallSet) * {QAlgorithms.gateT} = smallSet := by
  rw [Set.mul_singleton, Set.singleton_mul]
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨s, ⟨w, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨s', hs', he⟩ := g73p_rT w
    show QAlgorithms.gateT * _ * QAlgorithms.gateT ∈ smallSet
    rw [mul_assoc, he, ← mul_assoc, g73p_t5]
    exact g73p_smul (by simpa [smallLetterMatrix] using g73p_sm [.s]) hs'
  · rintro B ⟨w, rfl⟩
    obtain ⟨C, hC, he⟩ := g73p_lT w
    refine ⟨_, ⟨([.s, .s, .s].map smallLetterMatrix).prod * C, g73p_smul (g73p_sm _) hC, rfl⟩, ?_⟩
    show QAlgorithms.gateT * (([.s, .s, .s].map smallLetterMatrix).prod * C) * QAlgorithms.gateT = _
    rw [mul_assoc, mul_assoc, ← he, ← mul_assoc, ← mul_assoc, g73p_t6, one_mul]

theorem g73p_coset :
    cliffordSet = transversal * smallSet ∧
    cliffordSet \ smallSet = nonidentityTransversal * smallSet ∧
    smallSet * nonidentityTransversal ⊆ nonidentityTransversal * smallSet ∧
    smallSet * {QAlgorithms.gateT} = {QAlgorithms.gateT} * smallSet ∧
    ({QAlgorithms.gateT} * smallSet) * {QAlgorithms.gateT} = smallSet :=
  ⟨g73p_part1, g73p_part2, g73p_part3, g73p_part4, g73p_part5⟩


/-- Lemma 2.2, equations (3)-(7), PDF p.2. All five operations are on SETS;
smallSet is the calligraphic subgroup, not the single S gate. -/
theorem solution :
    cliffordSet = transversal * smallSet ∧
    cliffordSet \ smallSet = nonidentityTransversal * smallSet ∧
    smallSet * nonidentityTransversal ⊆ nonidentityTransversal * smallSet ∧
    smallSet * {QAlgorithms.gateT} = {QAlgorithms.gateT} * smallSet ∧
    ({QAlgorithms.gateT} * smallSet) * {QAlgorithms.gateT} = smallSet := by
  exact g73p_coset


end
