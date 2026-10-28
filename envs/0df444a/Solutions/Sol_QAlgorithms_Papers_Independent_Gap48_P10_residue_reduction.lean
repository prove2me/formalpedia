-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.residue_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:53:03.646033+00:00
-- url     : https://prove2.me/submissions/91b6f464-e19b-4b40-a205-2178de875152

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_column_coefficient_identities
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_row_coefficient_identities
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_bloch_clifford_characterization
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_forbidden_unit_vector_residues

-- ===== P10A =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

lemma s2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma s2mul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
lemma s2ne : Real.sqrt 2 ≠ 0 := by positivity
lemma s2pow_ne (k : ℕ) : Real.sqrt 2 ^ k ≠ 0 := pow_ne_zero _ s2ne

lemma lin_sqrt (x y : ℤ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp at h
    exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have : Real.sqrt 2 = ((-x / y : ℚ) : ℝ) := by
      push_cast; field_simp; linarith
    exact irrational_sqrt_two ⟨_, this.symm⟩

lemma coeff_unique (a b c d : ℤ) (h : (a : ℝ) + b * Real.sqrt 2 = c + d * Real.sqrt 2) :
    a = c ∧ b = d := by
  have := lin_sqrt (a - c) (b - d) (by push_cast; linarith)
  omega

lemma quad_eq (a b : ℤ) : quadraticCoordinates ((a : ℝ) + b * Real.sqrt 2) = (a, b) := by
  have h : ∃ ab : ℤ × ℤ, ((a : ℝ) + b * Real.sqrt 2) = (ab.1 : ℝ) + (ab.2 : ℝ) * Real.sqrt 2 :=
    ⟨(a, b), rfl⟩
  unfold quadraticCoordinates
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  obtain ⟨h1, h2⟩ := coeff_unique _ _ _ _ hs
  exact Prod.ext h1.symm h2.symm

lemma parity_eq (a b : ℤ) : parity ((a : ℝ) + b * Real.sqrt 2) = (a : ZMod 2) := by
  simp [parity, quad_eq]

/-! Z[√2] closure -/

lemma Z_add {x y : ℝ} (hx : InZsqrt2 x) (hy : InZsqrt2 y) : InZsqrt2 (x + y) := by
  obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a + c, b + d, by push_cast; ring⟩

lemma Z_mul {x y : ℝ} (hx : InZsqrt2 x) (hy : InZsqrt2 y) : InZsqrt2 (x * y) := by
  obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a * c + 2 * b * d, a * d + b * c, by push_cast; linear_combination (b * d : ℝ) * s2mul⟩

lemma Z_neg {x : ℝ} (hx : InZsqrt2 x) : InZsqrt2 (-x) := by
  obtain ⟨a, b, rfl⟩ := hx
  exact ⟨-a, -b, by push_cast; ring⟩

lemma Z_int (n : ℤ) : InZsqrt2 n := ⟨n, 0, by simp⟩
lemma Z_zero : InZsqrt2 0 := ⟨0, 0, by simp⟩
lemma Z_one : InZsqrt2 1 := ⟨1, 0, by simp⟩
lemma Z_s2 : InZsqrt2 (Real.sqrt 2) := ⟨0, 1, by simp⟩

lemma Z_sum (f : Fin 3 → ℝ) (h : ∀ i, InZsqrt2 (f i)) : InZsqrt2 (∑ i, f i) := by
  rw [Fin.sum_univ_three]; exact Z_add (Z_add (h 0) (h 1)) (h 2)

lemma Z_s2mul {x : ℝ} (hx : InZsqrt2 x) : InZsqrt2 (Real.sqrt 2 * x) := Z_mul Z_s2 hx

lemma Z_pow_mul {x : ℝ} (hx : InZsqrt2 x) (m : ℕ) : InZsqrt2 (Real.sqrt 2 ^ m * x) := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ', mul_assoc]; exact Z_s2mul ih

/-! denominators and lde -/

lemma den_mono {U : RealMat} {k : ℕ} (h : realDenominator U k) (m : ℕ) :
    realDenominator U (k + m) := by
  intro i j
  rw [pow_add, mul_comm (Real.sqrt 2 ^ k), mul_assoc]
  exact Z_pow_mul (h i j) m

lemma den_mono' {U : RealMat} {k l : ℕ} (h : realDenominator U k) (hl : k ≤ l) :
    realDenominator U l := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
  exact den_mono h m

lemma den_exists (U : RealMat) (hring : ∀ i j, InDsqrt2 (U i j)) : ∃ k, realDenominator U k := by
  choose K hK using hring
  refine ⟨∑ i, ∑ j, K i j, fun i j => ?_⟩
  have hle : K i j ≤ ∑ i, ∑ j, K i j :=
    (Finset.single_le_sum (f := fun j => K i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, K i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
  rw [hm, pow_add, mul_comm (Real.sqrt 2 ^ K i j), mul_assoc]
  exact Z_pow_mul (hK i j) m

lemma lde_spec (U : RealMat) (h : ∃ k, realDenominator U k) : realDenominator U (realLde U) := by
  unfold realLde; rw [dif_pos h]; exact Nat.find_spec h

lemma lde_min (U : RealMat) {j : ℕ} (hj : realDenominator U j) : realLde U ≤ j := by
  have h : ∃ k, realDenominator U k := ⟨j, hj⟩
  unfold realLde; rw [dif_pos h]; exact Nat.find_min' h hj

lemma lde_eq (U : RealMat) {k : ℕ} (hk : realDenominator U k)
    (hmin : ∀ j, realDenominator U j → k ≤ j) : realLde U = k :=
  le_antisymm (lde_min U hk) (hmin _ (lde_spec U ⟨k, hk⟩))

lemma coeffs {U : RealMat} {k : ℕ} (h : realDenominator U k) :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℤ, ∀ i j,
      U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k := by
  choose A B hAB using h
  refine ⟨A, B, fun i j => ?_⟩
  rw [← hAB i j]; field_simp [s2pow_ne k]

/-! parity shape (finite check) -/

/-- excluded row for pattern r is r+2; ones at rows ≠ r+2 and columns ≠ c. -/
def shape (r c : Fin 3) (i j : Fin 3) : ZMod 2 := if i ≠ r + 2 ∧ j ≠ c then 1 else 0

set_option maxRecDepth 100000 in
lemma check9 : ∀ a b c d e f g h k : ZMod 2,
    (∀ j, (![![a, b, c], ![d, e, f], ![g, h, k]] : Fin 3 → Fin 3 → ZMod 2) 0 j +
      ![![a, b, c], ![d, e, f], ![g, h, k]] 1 j + ![![a, b, c], ![d, e, f], ![g, h, k]] 2 j = 0) →
    (∀ i, (![![a, b, c], ![d, e, f], ![g, h, k]] : Fin 3 → Fin 3 → ZMod 2) i 0 +
      ![![a, b, c], ![d, e, f], ![g, h, k]] i 1 + ![![a, b, c], ![d, e, f], ![g, h, k]] i 2 = 0) →
    (∀ j l, j ≠ l →
      (![![a, b, c], ![d, e, f], ![g, h, k]] : Fin 3 → Fin 3 → ZMod 2) 0 j *
        ![![a, b, c], ![d, e, f], ![g, h, k]] 0 l +
      ![![a, b, c], ![d, e, f], ![g, h, k]] 1 j * ![![a, b, c], ![d, e, f], ![g, h, k]] 1 l +
      ![![a, b, c], ![d, e, f], ![g, h, k]] 2 j * ![![a, b, c], ![d, e, f], ![g, h, k]] 2 l = 0) →
    (∃ i j, (![![a, b, c], ![d, e, f], ![g, h, k]] : Fin 3 → Fin 3 → ZMod 2) i j ≠ 0) →
    ∃ r c', ∀ i j, (![![a, b, c], ![d, e, f], ![g, h, k]] : Fin 3 → Fin 3 → ZMod 2) i j =
      shape r c' i j := by
  unfold shape
  decide

lemma shape_check (P : Fin 3 → Fin 3 → ZMod 2)
    (h1 : ∀ j, P 0 j + P 1 j + P 2 j = 0)
    (h2 : ∀ i, P i 0 + P i 1 + P i 2 = 0)
    (h3 : ∀ j l, j ≠ l → P 0 j * P 0 l + P 1 j * P 1 l + P 2 j * P 2 l = 0)
    (h4 : ∃ i j, P i j ≠ 0) :
    ∃ r c, ∀ i j, P i j = shape r c i j := by
  have hP : P = ![![P 0 0, P 0 1, P 0 2], ![P 1 0, P 1 1, P 1 2], ![P 2 0, P 2 1, P 2 2]] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hP] at h1 h2 h3 h4 ⊢
  exact check9 _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

end X4P10

-- ===== P10D =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

lemma omega_eq : Complex.exp (Complex.I * Real.pi / 4) =
    ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ := by
  have : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  apply Complex.ext <;> simp

def cT : ℝ := Real.sqrt 2 / 2

def BT : RealMat := !![cT, -cT, 0; cT, cT, 0; 0, 0, 1]

lemma bloch_T : operatorBloch QAlgorithms.gateT = BT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [operatorBloch, BT, cT, QAlgorithms.gateT, omega_eq, QAlgorithms.QubitChannels.sigma,
    QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_bool, Matrix.diagonal, Matrix.conjTranspose_apply] <;> ring_nf <;> simp <;> ring_nf

def BHT : RealMat := !![0, 0, 1; -cT, -cT, 0; cT, -cT, 0]
def BSHT : RealMat := !![cT, cT, 0; 0, 0, 1; cT, -cT, 0]

lemma s2c : ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  have h : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp; rw [Real.sq_sqrt (by norm_num)]
  rw [← h]; push_cast; rfl

lemma bloch_HT : operatorBloch (QAlgorithms.hadamard * QAlgorithms.gateT) = BHT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [operatorBloch, BHT, cT, QAlgorithms.gateT, QAlgorithms.hadamard, omega_eq, s2c,
    QAlgorithms.QubitChannels.sigma,
    QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_bool, Matrix.diagonal, Matrix.conjTranspose_apply] <;> ring_nf <;> simp <;> ring_nf <;>
    linear_combination (1/4 + (Real.sqrt 2 ^ 2 + 2)/8) * s2sq

lemma bloch_SHT : operatorBloch (QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.gateT) = BSHT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [operatorBloch, BSHT, cT, QAlgorithms.gateT, QAlgorithms.hadamard, QAlgorithms.phaseS, omega_eq, s2c,
    QAlgorithms.QubitChannels.sigma,
    QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_bool, Matrix.diagonal, Matrix.conjTranspose_apply] <;> ring_nf <;> simp <;> ring_nf <;>
    linear_combination (1/4 + (Real.sqrt 2 ^ 2 + 2)/8) * s2sq

end X4P10

-- ===== P10L =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

/-! Z[ω] coordinates (groundwork for Lemma 7.8) -/

lemma om_eq : QAlgorithms.gateT true true = ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ := by
  simp [QAlgorithms.gateT, omega_eq]

lemma ocv_re (a : Fin 4 → ℤ) :
    (omegaCoordinatesValue a).re = a 3 + (a 2 - a 0) * (Real.sqrt 2 / 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := s2sq
  simp [omegaCoordinatesValue, om_eq, pow_succ, Complex.mul_re, Complex.mul_im]
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, h2]
  ring_nf; rw [h3]; try rw [h2]
  ring

lemma ocv_im (a : Fin 4 → ℤ) :
    (omegaCoordinatesValue a).im = a 1 + (a 0 + a 2) * (Real.sqrt 2 / 2) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := s2sq
  simp [omegaCoordinatesValue, om_eq, pow_succ, Complex.mul_re, Complex.mul_im]
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, h2]
  ring_nf; rw [h3]; try rw [h2]
  ring

lemma ocv_inj (a b : Fin 4 → ℤ) (h : omegaCoordinatesValue a = omegaCoordinatesValue b) : a = b := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  rw [ocv_re, ocv_re] at hr
  rw [ocv_im, ocv_im] at hi
  obtain ⟨r1, r2⟩ := lin_sqrt (2 * (a 3 - b 3)) ((a 2 - a 0) - (b 2 - b 0)) (by push_cast; linarith)
  obtain ⟨i1, i2⟩ := lin_sqrt (2 * (a 1 - b 1)) ((a 0 + a 2) - (b 0 + b 2)) (by push_cast; linarith)
  funext j
  fin_cases j <;> simp <;> omega

lemma coords_eq (a : Fin 4 → ℤ) : omegaCoordinates (omegaCoordinatesValue a) = a := by
  have h : InZomega (omegaCoordinatesValue a) := ⟨a, rfl⟩
  unfold omegaCoordinates
  rw [dif_pos h]
  exact ocv_inj _ _ (Classical.choose_spec h)

lemma residue_eq (a : Fin 4 → ℤ) : residue (omegaCoordinatesValue a) = fun j => (a j : ZMod 2) := by
  funext j; simp [residue, coords_eq]

end X4P10

-- ===== P10G =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

lemma pauli_expand (X : Mat) (hH : X.conjTranspose = X) (htr : X.trace = 0) :
    X = ∑ m : Fin 3, (((Matrix.trace (QAlgorithms.QubitChannels.sigma m * X)).re / 2 : ℝ) : ℂ) •
      QAlgorithms.QubitChannels.sigma m := by
  have h1 := congrFun (congrFun hH false) false
  have h2 := congrFun (congrFun hH true) true
  have h3 := congrFun (congrFun hH true) false
  simp [Matrix.conjTranspose_apply] at h1 h2 h3
  have ht : X false false + X true true = 0 := by
    simpa [Matrix.trace, Fintype.sum_bool, add_comm] using htr
  have i1 : (X false false).im = 0 := by
    have := congrArg Complex.im h1; simp at this; linarith
  have i2 : (X true true).im = 0 := by
    have := congrArg Complex.im h2; simp at this; linarith
  have r3 := congrArg Complex.re h3
  have m3 := congrArg Complex.im h3
  simp at r3 m3
  have tr := congrArg Complex.re ht
  have ti := congrArg Complex.im ht
  simp at tr ti
  ext a b
  cases a <;> cases b <;>
    simp [Fin.sum_univ_three, QAlgorithms.QubitChannels.sigma, QAlgorithms.pauliX, QAlgorithms.pauliY,
      QAlgorithms.pauliZ, Matrix.trace, Matrix.mul_apply, Fintype.sum_bool] <;>
    apply Complex.ext <;> simp <;> linarith

lemma bloch_mul (U V : Mat) (hV : V ∈ Matrix.unitaryGroup Bool ℂ) :
    operatorBloch (U * V) = operatorBloch U * operatorBloch V := by
  ext i j
  have hVV : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hVV' : V * star V = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  set X := V * QAlgorithms.QubitChannels.sigma j * star V with hX
  have hsig : ∀ m, (QAlgorithms.QubitChannels.sigma m).conjTranspose = QAlgorithms.QubitChannels.sigma m := by
    intro m; fin_cases m <;> ext a b <;> cases a <;> cases b <;>
      simp [QAlgorithms.QubitChannels.sigma, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
        Matrix.conjTranspose_apply]
  have hsigtr : ∀ m, (QAlgorithms.QubitChannels.sigma m).trace = 0 := by
    intro m; fin_cases m <;>
      simp [QAlgorithms.QubitChannels.sigma, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
        Matrix.trace, Fintype.sum_bool]
  have hXH : X.conjTranspose = X := by
    rw [hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hsig]
    simp [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hXtr : X.trace = 0 := by
    rw [hX, Matrix.trace_mul_cycle, hVV, Matrix.one_mul, hsigtr]
  have hexp := pauli_expand X hXH hXtr
  have key : QAlgorithms.QubitChannels.sigma i * (U * V) * QAlgorithms.QubitChannels.sigma j * star (U * V) =
      QAlgorithms.QubitChannels.sigma i * U * X * star U := by
    rw [hX, StarMul.star_mul]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_apply]
  simp only [operatorBloch]
  rw [key, hexp]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [hX]
  simp only [Matrix.mul_assoc]
  ring

end X4P10

-- ===== P10B =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

lemma sum_rot {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (r : Fin 3) :
    ∑ i, f i = f r + f (r + 1) + f (r + 2) := by
  rw [Fin.sum_univ_three]
  fin_cases r <;> simp <;> abel

lemma z2_sq (x : ZMod 2) : x ^ 2 = x := by revert x; decide

lemma z2_eq_of_add (x y : ZMod 2) (h : x + y = 0) : x = y := by revert x y; decide

lemma int_sq_mod4_odd (a : ℤ) (h : (a : ZMod 2) = 1) : a ^ 2 % 4 = 1 := by
  have : Odd a := by
    rcases Int.even_or_odd a with he | ho
    · exfalso; rw [(ZMod.intCast_eq_zero_iff_even).2 he] at h; exact zero_ne_one h
    · exact ho
  exact Int.sq_mod_four_eq_one_of_odd this

lemma int_sq_mod4_even (a : ℤ) (h : (a : ZMod 2) = 0) : a ^ 2 % 4 = 0 := by
  obtain ⟨t, rfl⟩ := (ZMod.intCast_eq_zero_iff_even).1 h
  have : (t + t) ^ 2 = 4 * (t ^ 2) := by ring
  rw [this]; omega

lemma int_sq_mod2 (b : ℤ) : (b ^ 2 - b) % 2 = 0 := by
  have := Int.even_mul_pred_self b
  have e : b ^ 2 - b = b * (b - 1) := by ring
  rw [e]; exact Int.even_iff.1 this

lemma zmod2_iff (b : ℤ) : (b : ZMod 2) = ((b % 2 : ℤ) : ZMod 2) :=
  (ZMod.intCast_mod b 2).symm

/-- The b-coefficient at the even entry of a row with two odd entries depends only on k. -/
lemma rowfact (a b : Fin 3 → ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hs : ∑ j, a j * b j = 0) (hn : ∑ j, (a j ^ 2 + 2 * b j ^ 2) = 2 ^ k) (c : Fin 3)
    (hodd : ∀ j, j ≠ c → (a j : ZMod 2) = 1) (heven : (a c : ZMod 2) = 0) :
    (b c : ZMod 2) = if k = 1 then 0 else 1 := by
  have hs2 := congrArg (Int.cast : ℤ → ZMod 2) hs
  push_cast at hs2
  rw [sum_rot _ c] at hs2 hn
  have h1 := hodd (c + 1) (by fin_cases c <;> decide)
  have h2 := hodd (c + 2) (by fin_cases c <;> decide)
  rw [h1, h2, heven] at hs2
  simp only [zero_mul, one_mul, zero_add] at hs2
  have hb := z2_eq_of_add _ _ hs2
  have q1 := int_sq_mod4_odd _ h1
  have q2 := int_sq_mod4_odd _ h2
  have q0 := int_sq_mod4_even _ heven
  have r0 := int_sq_mod2 (b c)
  have r1 := int_sq_mod2 (b (c + 1))
  have r2 := int_sq_mod2 (b (c + 2))
  have hb' : b (c + 1) % 2 = b (c + 2) % 2 := by
    rw [zmod2_iff, zmod2_iff (b (c + 2))] at hb
    have := (ZMod.intCast_eq_intCast_iff' _ _ 2).1 hb
    simpa using this
  have hpow : (2 : ℤ) ^ k % 4 = if k = 1 then 2 else 0 := by
    split_ifs with h
    · subst h; norm_num
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
      rw [pow_add]; norm_num
  rw [zmod2_iff]
  generalize a c ^ 2 = X0 at *
  generalize a (c + 1) ^ 2 = X1 at *
  generalize a (c + 2) ^ 2 = X2 at *
  generalize b c ^ 2 = Y0 at *
  generalize b (c + 1) ^ 2 = Y1 at *
  generalize b (c + 2) ^ 2 = Y2 at *
  generalize (2 : ℤ) ^ k = K at *
  split_ifs at hpow ⊢ with h
  · have : b c % 2 = 0 := by omega
    rw [this]; rfl
  · have : b c % 2 = 1 := by omega
    rw [this]; rfl

/-- Main structural fact behind Lemmas 6.3/6.4. -/
theorem struct (U : RealMat) (hU : SpecialOrthogonal U) (hring : ∀ i j, InDsqrt2 (U i j))
    (hk : 0 < realLde U) :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℤ,
      (∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ realLde U) ∧
      ∃ r c : Fin 3, (∀ i j, (A i j : ZMod 2) = shape r c i j) ∧
        (∀ j, (B r j : ZMod 2) = B (r + 1) j) := by
  set k := realLde U with hkdef
  have hden := lde_spec U (den_exists U hring)
  obtain ⟨A, B, hAB⟩ := coeffs hden
  refine ⟨A, B, hAB, ?_⟩
  have hc := column_coefficient_identities U hU hring k A B hAB
  have hr := row_coefficient_identities U hU hring k A B hAB
  have t2 : (2 : ZMod 2) = 0 := rfl
  have h2k : (2 : ZMod 2) ^ k = 0 := by rw [t2]; exact zero_pow (by omega)
  set P : Fin 3 → Fin 3 → ZMod 2 := fun i j => (A i j : ZMod 2) with hP
  have H1 : ∀ j, P 0 j + P 1 j + P 2 j = 0 := by
    intro j
    have := congrArg (Int.cast : ℤ → ZMod 2) (hc.2 j).2
    push_cast [Fin.sum_univ_three] at this
    simp only [t2, zero_mul, add_zero, z2_sq, zero_pow (show k ≠ 0 by omega)] at this
    simpa [hP] using this
  have H2 : ∀ i, P i 0 + P i 1 + P i 2 = 0 := by
    intro i
    have := congrArg (Int.cast : ℤ → ZMod 2) (hr.2 i).2
    push_cast [Fin.sum_univ_three] at this
    simp only [t2, zero_mul, add_zero, z2_sq, zero_pow (show k ≠ 0 by omega)] at this
    simpa [hP] using this
  have H3 : ∀ j l, j ≠ l → P 0 j * P 0 l + P 1 j * P 1 l + P 2 j * P 2 l = 0 := by
    intro j l hjl
    have := congrArg (Int.cast : ℤ → ZMod 2) ((hc.1 j l).2)
    rw [if_neg hjl, mul_zero, Fin.sum_univ_three] at this
    push_cast at this
    simp only [t2, zero_mul, add_zero] at this
    simpa [hP] using this
  have H4 : ∃ i j, P i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hev : ∀ i j, Even (A i j) := fun i j => (ZMod.intCast_eq_zero_iff_even).1 (hcon i j)
    have : realDenominator U (k - 1) := by
      intro i j
      obtain ⟨t, ht⟩ := hev i j
      refine ⟨B i j, t, ?_⟩
      rw [hAB i j, ht, ← hkdef]
      have hk' : Real.sqrt 2 ^ k = Real.sqrt 2 ^ (k - 1) * Real.sqrt 2 := by
        rw [← pow_succ]; congr 1; omega
      rw [hk']
      have := s2pow_ne (k - 1)
      push_cast
      field_simp
      first | linear_combination (t : ℝ) * s2mul | linear_combination (-(t : ℝ)) * s2mul
    have := lde_min U this
    omega
  obtain ⟨r, c, hrc⟩ := shape_check P H1 H2 H3 H4
  refine ⟨r, c, hrc, fun j => ?_⟩
  have hodd : ∀ i j, i ≠ r + 2 → j ≠ c → P i j = 1 := by
    intro i j hi hj; rw [hrc]; simp [shape, hi, hj]
  have hev : ∀ j, P (r + 2) j = 0 := by intro j; rw [hrc]; simp [shape]
  have hevc : ∀ i, P i c = 0 := by intro i; rw [hrc]; simp [shape]
  have hr0 : r ≠ r + 2 := by fin_cases r <;> decide
  have hr1 : r + 1 ≠ r + 2 := by fin_cases r <;> decide
  by_cases hj : j = c
  · subst hj
    have e1 := rowfact (fun l => A r l) (fun l => B r l) k hk (hr.2 r).1 (hr.2 r).2 j
      (fun l hl => hodd r l hr0 hl) (hevc r)
    have e2 := rowfact (fun l => A (r + 1) l) (fun l => B (r + 1) l) k hk (hr.2 (r + 1)).1
      (hr.2 (r + 1)).2 j (fun l hl => hodd (r + 1) l hr1 hl) (hevc (r + 1))
    exact e1.trans e2.symm
  · have := congrArg (Int.cast : ℤ → ZMod 2) (hc.2 j).1
    push_cast at this
    rw [sum_rot _ r] at this
    have a0 : (A r j : ZMod 2) = 1 := hodd r j hr0 hj
    have a1 : (A (r + 1) j : ZMod 2) = 1 := hodd (r + 1) j hr1 hj
    have a2 : (A (r + 2) j : ZMod 2) = 0 := hev j
    rw [a0, a1, a2] at this
    simp only [one_mul, zero_mul, add_zero] at this
    exact z2_eq_of_add _ _ this

end X4P10

-- ===== P10E =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

lemma z2_pm (e : ℤ) (he : e = 1 ∨ e = -1) : (e : ZMod 2) = 1 := by
  rcases he with rfl | rfl <;> decide

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma pow_split (k : ℕ) (hk : 1 ≤ k) : Real.sqrt 2 ^ k = Real.sqrt 2 ^ (k - 1) * Real.sqrt 2 := by
  rw [← pow_succ]; congr 1; omega

lemma low_pair (k : ℕ) (hk : 1 ≤ k) (up uq v : ℝ) (ap aq bp bq e1 e2 : ℤ)
    (hup : up = ((ap : ℝ) + (bp : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k)
    (huq : uq = ((aq : ℝ) + (bq : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k)
    (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1)
    (ha : (ap : ZMod 2) = aq) (hb : (bp : ZMod 2) = bq)
    (hv : v = cT * ((e1 : ℝ) * up + (e2 : ℝ) * uq)) :
    InZsqrt2 (Real.sqrt 2 ^ (k - 1) * v) := by
  have h1 : Even (e1 * ap + e2 * aq) := by
    apply (ZMod.intCast_eq_zero_iff_even).1
    push_cast; rw [z2_pm e1 he1, z2_pm e2 he2, ha]; simp only [one_mul]; exact z2_add_self _
  have h2 : Even (e1 * bp + e2 * bq) := by
    apply (ZMod.intCast_eq_zero_iff_even).1
    push_cast; rw [z2_pm e1 he1, z2_pm e2 he2, hb]; simp only [one_mul]; exact z2_add_self _
  obtain ⟨t, ht⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  refine ⟨t, t', ?_⟩
  have e : Real.sqrt 2 ^ (k - 1) * v =
      (((e1 * ap + e2 * aq : ℤ) : ℝ) + ((e1 * bp + e2 * bq : ℤ) : ℝ) * Real.sqrt 2) / 2 := by
    rw [hv, hup, huq, pow_split k hk]
    have := s2pow_ne (k - 1)
    unfold cT
    field_simp
    push_cast
    ring
  rw [e, ht, ht']; push_cast; ring

lemma low_single (k : ℕ) (hk : 1 ≤ k) (ux v : ℝ) (ax bx e : ℤ)
    (hux : ux = ((ax : ℝ) + (bx : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k)
    (ha : (ax : ZMod 2) = 0) (hv : v = (e : ℝ) * ux) :
    InZsqrt2 (Real.sqrt 2 ^ (k - 1) * v) := by
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_zero_iff_even).1 ha
  refine ⟨e * bx, e * t, ?_⟩
  rw [hv, hux, pow_split k hk, ht]
  have := s2pow_ne (k - 1)
  field_simp
  push_cast
  linear_combination (-(e * t) : ℝ) * s2sq

lemma den_mul (L V : RealMat) (hL : ∀ a b, InZsqrt2 (Real.sqrt 2 * L a b)) {j : ℕ}
    (hV : realDenominator V j) : realDenominator (L * V) (j + 1) := by
  intro a b
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Z_sum
  intro m
  have : Real.sqrt 2 ^ (j + 1) * (L a m * V m b) = (Real.sqrt 2 * L a m) * (Real.sqrt 2 ^ j * V m b) := by
    ring
  rw [this]; exact Z_mul (hL a m) (hV m b)

lemma s2cT : Real.sqrt 2 * cT = 1 := by
  unfold cT; field_simp; try rw [s2sq]

lemma cT_sq : cT * cT = 1 / 2 := by
  unfold cT; field_simp; first | exact s2sq | (rw [s2sq]; norm_num) | skip

lemma Z_negone : InZsqrt2 (-1) := ⟨-1, 0, by simp⟩

lemma hL_T : ∀ a b, InZsqrt2 (Real.sqrt 2 * BT a b) := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [BT, s2cT, Z_zero, Z_one, Z_s2, Z_negone, mul_neg]

lemma hL_HT : ∀ a b, InZsqrt2 (Real.sqrt 2 * BHT a b) := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [BHT, s2cT, Z_zero, Z_one, Z_s2, Z_negone, mul_neg]

lemma hL_SHT : ∀ a b, InZsqrt2 (Real.sqrt 2 * BSHT a b) := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [BSHT, s2cT, Z_zero, Z_one, Z_s2, Z_negone, mul_neg]

lemma orth_T : BT * BT.transpose = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [BT, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> linear_combination 2 * cT_sq

lemma orth_HT : BHT * BHT.transpose = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [BHT, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> linear_combination 2 * cT_sq

lemma orth_SHT : BSHT * BSHT.transpose = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [BSHT, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> linear_combination 2 * cT_sq

/-- Lower bound: lde(Lᵀ U) ≥ lde U - 1 for the three Bloch syllables. -/
lemma lower_bound (L U : RealMat) (hL : ∀ a b, InZsqrt2 (Real.sqrt 2 * L a b)) (hO : L * L.transpose = 1)
    {j : ℕ} (hV : realDenominator (L.transpose * U) j) : realLde U ≤ j + 1 := by
  have := den_mul L _ hL hV
  rw [← Matrix.mul_assoc, hO, Matrix.one_mul] at this
  exact lde_min U this

end X4P10

-- ===== P10C =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

lemma shape_pattern : ∀ r c i j : Fin 3, shape r c i (Equiv.swap 2 c j) = parityPattern r i j := by
  intro r c i j
  fin_cases r <;> fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [shape, parityPattern, Equiv.swap_apply_def] <;> decide

lemma parity_of (U : RealMat) (A B : Matrix (Fin 3) (Fin 3) ℤ) (k : ℕ)
    (hAB : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k) (i j : Fin 3) :
    matrixParity U k i j = (A i j : ZMod 2) := by
  unfold matrixParity
  rw [hAB, mul_div_cancel₀ _ (s2pow_ne k), parity_eq]

lemma case_zero (U : RealMat) (hU : SpecialOrthogonal U) (hring : ∀ i j, InDsqrt2 (U i j))
    (h0 : realLde U = 0) : ∃ C : Clifford, operatorBloch C.val = U := by
  have hden := lde_spec U (den_exists U hring)
  rw [h0] at hden
  obtain ⟨A, B, hAB⟩ := coeffs hden
  have hc := column_coefficient_identities U hU hring 0 A B hAB
  refine ((bloch_clifford_characterization.2 U).1).2 ⟨hU, fun i j => ?_⟩
  have hn := (hc.2 j).2
  simp only [pow_zero, Fin.sum_univ_three] at hn
  have hb : B i j = 0 ∧ (A i j = -1 ∨ A i j = 0 ∨ A i j = 1) := by
    have p0 := sq_nonneg (A 0 j); have p1 := sq_nonneg (A 1 j); have p2 := sq_nonneg (A 2 j)
    have q0 := sq_nonneg (B 0 j); have q1 := sq_nonneg (B 1 j); have q2 := sq_nonneg (B 2 j)
    have hle : A i j ^ 2 + 2 * B i j ^ 2 ≤ 1 := by fin_cases i <;> simp <;> nlinarith
    have hB : B i j ^ 2 = 0 := by nlinarith [sq_nonneg (B i j), sq_nonneg (A i j)]
    have hA : A i j ^ 2 ≤ 1 := by nlinarith [sq_nonneg (B i j)]
    refine ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hB, ?_⟩
    have : -1 ≤ A i j ∧ A i j ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (A i j + 1), sq_nonneg (A i j - 1)]
    omega
  rw [hAB, hb.1]
  rcases hb.2 with h | h | h <;> simp [h]

theorem lemma63 (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) :
    (realLde U = 0 → ∃ C : Clifford, operatorBloch C.val = U) ∧
    (0 < realLde U → ∃ r : Fin 3,
      parityEquivalent (matrixParity U (realLde U)) (parityPattern r)) := by
  refine ⟨case_zero U hU hring, fun hk => ?_⟩
  obtain ⟨A, B, hAB, r, c, hsh, -⟩ := struct U hU hring hk
  refine ⟨r, Equiv.swap 2 c, fun i j => ?_⟩
  rw [parity_of U A B _ hAB, hsh, shape_pattern]

end X4P10

-- ===== P10H =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

lemma par_of {z : ℝ} {a b : ℤ} (h : z = (a : ℝ) + (b : ℝ) * Real.sqrt 2) : parity z = (a : ZMod 2) := by
  rw [h, parity_eq]

/-- If the parity matrix at a denominator exponent n ≥ 1 is nonzero, n is the least exponent. -/
lemma lde_of_odd (W : RealMat) (n : ℕ) (hn : 1 ≤ n) (hW : realDenominator W n)
    (hodd : ∃ i j, matrixParity W n i j ≠ 0) : realLde W = n := by
  apply lde_eq W hW
  intro j hj
  by_contra hlt
  push_neg at hlt
  have h' : realDenominator W (n - 1) := den_mono' hj (by omega)
  obtain ⟨i, l, hil⟩ := hodd
  obtain ⟨a, b, hab⟩ := h' i l
  apply hil
  have : Real.sqrt 2 ^ n * W i l = ((2 * b : ℤ) : ℝ) + (a : ℝ) * Real.sqrt 2 := by
    rw [show n = (n - 1) + 1 by omega, pow_succ, mul_comm (Real.sqrt 2 ^ (n - 1)), mul_assoc, hab]
    push_cast; linear_combination (b : ℝ) * s2mul
  unfold matrixParity
  rw [par_of this]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

lemma pair_entry (n : ℕ) (w0 w1 v : ℝ) (e1 e2 : ℤ) (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1)
    (h0 : InZsqrt2 (Real.sqrt 2 ^ n * w0)) (h1 : InZsqrt2 (Real.sqrt 2 ^ n * w1))
    (hv : v = cT * ((e1 : ℝ) * w0 + (e2 : ℝ) * w1)) :
    InZsqrt2 (Real.sqrt 2 ^ (n + 1) * v) ∧
      parity (Real.sqrt 2 ^ (n + 1) * v) =
        parity (Real.sqrt 2 ^ n * w0) + parity (Real.sqrt 2 ^ n * w1) := by
  obtain ⟨a0, b0, hab0⟩ := h0
  obtain ⟨a1, b1, hab1⟩ := h1
  have e : Real.sqrt 2 ^ (n + 1) * v =
      ((e1 * a0 + e2 * a1 : ℤ) : ℝ) + ((e1 * b0 + e2 * b1 : ℤ) : ℝ) * Real.sqrt 2 := by
    have : Real.sqrt 2 ^ (n + 1) * v =
        (Real.sqrt 2 * cT) * ((e1 : ℝ) * (Real.sqrt 2 ^ n * w0) + (e2 : ℝ) * (Real.sqrt 2 ^ n * w1)) := by
      rw [hv, pow_succ]; ring
    rw [this, s2cT, hab0, hab1]; push_cast; ring
  refine ⟨⟨_, _, e⟩, ?_⟩
  rw [par_of e, par_of hab0, par_of hab1]
  push_cast
  rw [z2_pm e1 he1, z2_pm e2 he2, one_mul, one_mul]

lemma single_entry (n : ℕ) (w v : ℝ) (e : ℤ) (h : InZsqrt2 (Real.sqrt 2 ^ n * w)) (hv : v = (e : ℝ) * w) :
    InZsqrt2 (Real.sqrt 2 ^ (n + 1) * v) ∧ parity (Real.sqrt 2 ^ (n + 1) * v) = 0 := by
  obtain ⟨a, b, hab⟩ := h
  have ee : Real.sqrt 2 ^ (n + 1) * v = ((2 * e * b : ℤ) : ℝ) + ((e * a : ℤ) : ℝ) * Real.sqrt 2 := by
    have : Real.sqrt 2 ^ (n + 1) * v = Real.sqrt 2 * (e : ℝ) * (Real.sqrt 2 ^ n * w) := by
      rw [hv, pow_succ]; ring
    rw [this, hab]; push_cast; linear_combination (e * b : ℝ) * s2mul
  refine ⟨⟨_, _, ee⟩, ?_⟩
  rw [par_of ee]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl]; simp

/-- the three Bloch syllables T, HT, SHT -/
def BL (r : Fin 3) : RealMat := if r = 0 then BT else if r = 1 then BHT else BSHT

lemma step (r : Fin 3) (W : RealMat) (n : ℕ) (hW : realDenominator W n) :
    realDenominator (BL r * W) (n + 1) ∧
      ∀ i j, matrixParity (BL r * W) (n + 1) i j =
        if i = r + 2 then 0 else matrixParity W n 0 j + matrixParity W n 1 j := by
  have key : ∀ i j, InZsqrt2 (Real.sqrt 2 ^ (n + 1) * (BL r * W) i j) ∧
      parity (Real.sqrt 2 ^ (n + 1) * (BL r * W) i j) =
        if i = r + 2 then 0 else matrixParity W n 0 j + matrixParity W n 1 j := by
    intro i j
    simp only [matrixParity]
    obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
    all_goals try (obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp)
    · have h := pair_entry n (W 0 j) (W 1 j) ((BL 0 * W) 0 j) (1) (-1) (Or.inl rfl) (Or.inr rfl) (hW 0 j) (hW 1 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := pair_entry n (W 0 j) (W 1 j) ((BL 0 * W) 1 j) (1) (1) (Or.inl rfl) (Or.inl rfl) (hW 0 j) (hW 1 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := single_entry n (W 2 j) ((BL 0 * W) 2 j) 1 (hW 2 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three])
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := single_entry n (W 2 j) ((BL 1 * W) 0 j) 1 (hW 2 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three])
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := pair_entry n (W 0 j) (W 1 j) ((BL 1 * W) 1 j) (-1) (-1) (Or.inr rfl) (Or.inr rfl) (hW 0 j) (hW 1 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := pair_entry n (W 0 j) (W 1 j) ((BL 1 * W) 2 j) (1) (-1) (Or.inl rfl) (Or.inr rfl) (hW 0 j) (hW 1 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := pair_entry n (W 0 j) (W 1 j) ((BL 2 * W) 0 j) (1) (1) (Or.inl rfl) (Or.inl rfl) (hW 0 j) (hW 1 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := single_entry n (W 2 j) ((BL 2 * W) 1 j) 1 (hW 2 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three])
      exact ⟨h.1, h.2.trans (by simp)⟩
    · have h := pair_entry n (W 0 j) (W 1 j) ((BL 2 * W) 2 j) (1) (-1) (Or.inl rfl) (Or.inr rfl) (hW 0 j) (hW 1 j)
        (by simp [BL, BT, BHT, BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
      exact ⟨h.1, h.2.trans (by simp)⟩
  exact ⟨fun i j => (key i j).1, fun i j => (key i j).2⟩

end X4P10

-- ===== P10I =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-! unitarity -/

lemma unit_T : QAlgorithms.gateT ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h : (Real.sqrt 2 / 2) ^ 2 * 2 = 1 := by
    rw [div_pow, s2sq]; norm_num
  ext a b
  cases a <;> cases b <;>
    simp [QAlgorithms.gateT, omega_eq, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal,
      Matrix.star_apply] <;> apply Complex.ext <;> simp <;> nlinarith [h]

lemma unit_of (x : ℝ) (hx : x ^ 2 * 2 = 1) :
    (Matrix.of fun a b : Bool => if a && b then -((x : ℂ)) else (x : ℂ)) ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Complex.conj_ofReal] <;>
    apply Complex.ext <;> simp <;> nlinarith [hx]

lemma unit_H : QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  have e : QAlgorithms.hadamard = Matrix.of fun a b : Bool =>
      if a && b then -(((Real.sqrt 2 / 2 : ℝ) : ℂ)) else ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    unfold QAlgorithms.hadamard; rw [s2c]
  rw [e]
  apply unit_of
  rw [div_pow, s2sq]; norm_num

lemma unit_S : QAlgorithms.phaseS ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  cases a <;> cases b <;>
    simp [QAlgorithms.phaseS, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal, Matrix.star_apply]

lemma unit_W : scalarOmega ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h : (Real.sqrt 2 / 2) ^ 2 * 2 = 1 := by
    rw [div_pow, s2sq]; norm_num
  ext a b
  cases a <;> cases b <;>
    simp [scalarOmega, QAlgorithms.gateT, omega_eq, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal,
      Matrix.star_apply, Matrix.one_apply] <;> apply Complex.ext <;> simp <;> nlinarith [h]

lemma unit_word (w : List CliffordLetter) : cliffordWordMatrix w ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold cliffordWordMatrix
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Submonoid.mul_mem _ ?_ ih
    cases a
    · exact unit_H
    · exact unit_S
    · exact unit_W

lemma unit_cliff (C : Clifford) : C.val ∈ Matrix.unitaryGroup Bool ℂ := by
  obtain ⟨w, hw⟩ := C.property
  rw [← hw]; exact unit_word w

/-! normal-form values -/

def syl (q : Bool) : List Token := [Token.clifford (if q then cliffordSH else cliffordH), Token.t]

def R (body : List Bool) (C : Clifford) : Mat :=
  ((body.flatMap syl ++ [Token.clifford C]).map tokenMatrix).prod

lemma H_val : cliffordH.val = QAlgorithms.hadamard := by
  simp [cliffordH, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix]

lemma SH_val : cliffordSH.val = QAlgorithms.phaseS * QAlgorithms.hadamard := by
  simp [cliffordSH, cliffordOfWord, cliffordWordMatrix, cliffordLetterMatrix]

lemma R_nil (C : Clifford) : R [] C = C.val := by simp [R, tokenMatrix]

lemma R_cons (q : Bool) (body : List Bool) (C : Clifford) :
    R (q :: body) C = (if q then QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.gateT
      else QAlgorithms.hadamard * QAlgorithms.gateT) * R body C := by
  simp only [R, List.flatMap_cons, List.append_assoc, List.map_append, List.prod_append]
  cases q <;> simp [syl, tokenMatrix, H_val, SH_val, Matrix.mul_assoc]

lemma maValue_eq (M : NormalForm) :
    maValue M = (if M.leadingT then QAlgorithms.gateT else 1) * R M.body M.terminal := by
  obtain ⟨lt, body, C⟩ := M
  simp only [maValue, normalValue, normalTokens, R]
  rw [List.append_assoc, List.map_append, List.prod_append]
  congr 1
  cases lt <;> simp [tokenMatrix]

lemma unit_R (body : List Bool) (C : Clifford) : R body C ∈ Matrix.unitaryGroup Bool ℂ := by
  induction body with
  | nil => rw [R_nil]; exact unit_cliff C
  | cons q body ih =>
    rw [R_cons]
    refine Submonoid.mul_mem _ ?_ ih
    cases q
    · exact Submonoid.mul_mem _ unit_H unit_T
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ unit_S unit_H) unit_T

/-! the invariant -/

lemma parity_zero : parity 0 = 0 := by
  have := parity_eq 0 0; simpa using this
lemma parity_one : parity 1 = 1 := by
  have := parity_eq 1 0; simpa using this
lemma parity_neg_one : parity (-1) = 1 := by
  have := parity_eq (-1) 0; simp at this; rw [this]

def Good (W : RealMat) (n : ℕ) : Prop :=
  ∃ c : Fin 3, ∀ j, matrixParity W n 0 j + matrixParity W n 1 j = if j ≠ c then 1 else 0

lemma good_cliff (C : Clifford) :
    realDenominator (operatorBloch C.val) 0 ∧ Good (operatorBloch C.val) 0 := by
  have hc := (bloch_clifford_characterization.2 (operatorBloch C.val)).1.1 ⟨C, rfl⟩
  obtain ⟨⟨h1, h2, -⟩, hent⟩ := hc
  set W := operatorBloch C.val
  constructor
  · intro i j
    simp only [pow_zero, one_mul]
    rcases hent i j with h | h | h <;> rw [h]
    · exact Z_neg Z_one
    · exact Z_zero
    · exact Z_one
  · have col : ∀ j, W 0 j * W 0 j + W 1 j * W 1 j + W 2 j * W 2 j = 1 := by
      intro j
      have := congrFun (congrFun h1 j) j
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have row : W 2 0 * W 2 0 + W 2 1 * W 2 1 + W 2 2 * W 2 2 = 1 := by
      have := congrFun (congrFun h2 2) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
    have hc : ∃ c, W 2 c ≠ 0 := by
      by_contra hh
      push_neg at hh
      rw [hh 0, hh 1, hh 2] at row; norm_num at row
    obtain ⟨c, hc⟩ := hc
    have hz : ∀ j, j ≠ c → W 2 j = 0 := by
      intro j hj
      have sq : ∀ l, W 2 l * W 2 l = 0 ∨ W 2 l * W 2 l = 1 := by
        intro l; rcases hent 2 l with h | h | h <;> rw [h] <;> norm_num
      have hc1 : W 2 c * W 2 c = 1 := by
        rcases sq c with h | h
        · exact absurd (mul_self_eq_zero.1 h) hc
        · exact h
      by_contra hne
      have hj1 : W 2 j * W 2 j = 1 := by
        rcases sq j with h | h
        · exact absurd (mul_self_eq_zero.1 h) hne
        · exact h
      have p0 := mul_self_nonneg (W 2 0); have p1 := mul_self_nonneg (W 2 1)
      have p2 := mul_self_nonneg (W 2 2)
      fin_cases c <;> fin_cases j <;> simp_all <;> linarith
    refine ⟨c, fun j => ?_⟩
    simp only [matrixParity, pow_zero, one_mul]
    have cj := col j
    by_cases hj : j = c
    · subst hj
      have h2 : W 2 j * W 2 j = 1 := by
        rcases hent 2 j with h | h | h
        · rw [h]; norm_num
        · exact absurd h hc
        · rw [h]; norm_num
      have e0 : W 0 j = 0 ∧ W 1 j = 0 := by
        constructor <;> nlinarith [mul_self_nonneg (W 0 j), mul_self_nonneg (W 1 j)]
      rw [e0.1, e0.2, parity_zero]; simp
    · rw [hz j hj] at cj
      simp only [if_pos hj]
      rcases hent 0 j with h | h | h <;> rcases hent 1 j with h' | h' | h' <;> rw [h, h'] at cj ⊢ <;>
        norm_num at cj <;> simp [parity_zero, parity_one, parity_neg_one] <;> rfl

lemma shape_good (r c : Fin 3) (hr : r = 1 ∨ r = 2) (W : RealMat) (n : ℕ)
    (h : ∀ i j, matrixParity W n i j = shape r c i j) : Good W n := by
  refine ⟨c, fun j => ?_⟩
  rw [h, h]
  rcases hr with rfl | rfl <;> by_cases hj : j = c <;> simp [shape, hj] <;> decide


lemma inv (body : List Bool) (C : Clifford) :
    realDenominator (operatorBloch (R body C)) body.length ∧ Good (operatorBloch (R body C)) body.length ∧
    (∀ q rest, body = q :: rest → ∃ c, ∀ i j,
      matrixParity (operatorBloch (R body C)) body.length i j = shape (if q then 2 else 1) c i j) := by
  induction body with
  | nil =>
    rw [R_nil]
    exact ⟨(good_cliff C).1, (good_cliff C).2, fun q rest h => nomatch h⟩
  | cons q rest ih =>
    obtain ⟨hd, ⟨c, hc⟩, -⟩ := ih
    have hB : operatorBloch (R (q :: rest) C) = BL (if q then 2 else 1) * operatorBloch (R rest C) := by
      rw [R_cons, bloch_mul _ _ (unit_R rest C)]
      cases q
      · simp [BL, bloch_HT]
      · simp [BL, bloch_SHT]
    obtain ⟨hd', hp'⟩ := step (if q then 2 else 1) _ _ hd
    have hsh : ∀ i j, matrixParity (operatorBloch (R (q :: rest) C)) (q :: rest).length i j =
        shape (if q then 2 else 1) c i j := by
      intro i j
      rw [hB, List.length_cons, hp', hc]
      cases q <;> fin_cases i <;> by_cases hj : j = c <;> simp [shape, hj] <;> decide
    refine ⟨by rw [hB, List.length_cons]; exact hd', ?_, ?_⟩
    · exact shape_good _ c (by cases q <;> simp) _ _ hsh
    · intro q' rest' h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨c, hsh⟩

end X4P10

-- ===== P10M =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true

/-! Z[ω] arithmetic and the residue ring homomorphism -/

lemma om2 : (ω) ^ 2 = Complex.I := by
  rw [om_eq]; apply Complex.ext <;> simp [pow_two, s2mul] <;> ring_nf <;> rw [s2sq] <;> norm_num

lemma om4 : (ω) ^ 4 = -1 := by
  rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, om2, Complex.I_sq]

def mulc (a b : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0,
    a 1 * b 3 + a 2 * b 2 + a 3 * b 1 - a 0 * b 0,
    a 2 * b 3 + a 3 * b 2 - a 0 * b 1 - a 1 * b 0,
    a 3 * b 3 - a 0 * b 2 - a 1 * b 1 - a 2 * b 0]

lemma ocv_add (a b : Fin 4 → ℤ) :
    omegaCoordinatesValue a + omegaCoordinatesValue b = omegaCoordinatesValue (a + b) := by
  simp [omegaCoordinatesValue]; ring

lemma ocv_neg (a : Fin 4 → ℤ) :
    -omegaCoordinatesValue a = omegaCoordinatesValue (-a) := by
  simp [omegaCoordinatesValue]; ring

lemma ocv_mul (a b : Fin 4 → ℤ) :
    omegaCoordinatesValue a * omegaCoordinatesValue b = omegaCoordinatesValue (mulc a b) := by
  simp only [omegaCoordinatesValue, mulc]
  simp
  linear_combination ((a 0 : ℂ) * b 0 * (ω) ^ 2 + ((a 0 : ℂ) * b 1 + a 1 * b 0) * (ω) +
    ((a 0 : ℂ) * b 2 + a 1 * b 1 + a 2 * b 0)) * om4

lemma Zw_add {x y : ℂ} (hx : InZomega x) (hy : InZomega y) : InZomega (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, (ocv_add a b).symm⟩

lemma Zw_neg {x : ℂ} (hx : InZomega x) : InZomega (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, (ocv_neg a).symm⟩

lemma Zw_mul {x y : ℂ} (hx : InZomega x) (hy : InZomega y) : InZomega (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨mulc a b, (ocv_mul a b).symm⟩

lemma ocv_zero : omegaCoordinatesValue 0 = 0 := by simp [omegaCoordinatesValue]
lemma ocv_one : omegaCoordinatesValue ![0, 0, 0, 1] = 1 := by simp [omegaCoordinatesValue]
lemma ocv_om : omegaCoordinatesValue ![0, 0, 1, 0] = ω := by simp [omegaCoordinatesValue]
lemma ocv_I : omegaCoordinatesValue ![0, 1, 0, 0] = Complex.I := by simp [omegaCoordinatesValue, om2]

lemma ocv_s2 : omegaCoordinatesValue ![-1, 0, 1, 0] = ((Real.sqrt 2 : ℝ) : ℂ) := by
  simp [omegaCoordinatesValue]
  rw [pow_succ, om2, om_eq]; apply Complex.ext <;> simp <;> ring

lemma Zw_zero : InZomega 0 := ⟨0, ocv_zero⟩
lemma Zw_one : InZomega 1 := ⟨_, ocv_one⟩
lemma Zw_om : InZomega ω := ⟨_, ocv_om⟩
lemma Zw_I : InZomega Complex.I := ⟨_, ocv_I⟩
lemma Zw_s2 : InZomega ((Real.sqrt 2 : ℝ) : ℂ) := ⟨_, ocv_s2⟩

lemma res_add {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    residue (x + y) = residue x + residue y := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  rw [ocv_add, residue_eq, residue_eq, residue_eq]; funext j; simp

lemma res_mul {x y : ℂ} (hx : InZomega x) (hy : InZomega y) :
    residue (x * y) = residueMultiply (residue x) (residue y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
  rw [ocv_mul, residue_eq, residue_eq, residue_eq]
  funext l
  fin_cases l <;> simp [residueMultiply, Fin.sum_univ_four, mulc, CharTwo.neg_eq, CharTwo.sub_eq_add] <;> ring

lemma res_zero : residue 0 = 0 := by
  rw [← ocv_zero, residue_eq]; funext j; simp

lemma res_sum {f : Bool → ℂ} (hf : ∀ l, InZomega (f l)) :
    residue (∑ l, f l) = ∑ l, residue (f l) := by
  simp only [Fintype.sum_bool]; exact res_add (hf true) (hf false)

lemma res_one : residue 1 = bits 1 := by
  rw [← ocv_one, residue_eq]; funext j; fin_cases j <;> rfl
lemma res_om : residue ω = bits 2 := by
  rw [← ocv_om, residue_eq]; funext j; fin_cases j <;> rfl
lemma res_I : residue Complex.I = bits 4 := by
  rw [← ocv_I, residue_eq]; funext j; fin_cases j <;> rfl
lemma res_s2 : residue ((Real.sqrt 2 : ℝ) : ℂ) = bits 10 := by
  rw [← ocv_s2, residue_eq]; funext j; fin_cases j <;> decide

end X4P10

-- ===== P10N =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true

/-! Matrix residues and the 64-element subgroup -/

lemma denW_mul {U B : Mat} {k : ℕ} (hU : complexDenominator U k) (hB : ∀ l j, InZomega (B l j)) :
    complexDenominator (U * B) k := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum, Fintype.sum_bool]
  rw [← mul_assoc, ← mul_assoc]
  exact Zw_add (Zw_mul (hU _ _) (hB _ _)) (Zw_mul (hU _ _) (hB _ _))

lemma den_succ {U : Mat} {k : ℕ} (hU : complexDenominator U k) : complexDenominator U (k + 1) := by
  intro i j
  rw [pow_succ, mul_comm _ ((Real.sqrt 2 : ℝ) : ℂ), mul_assoc]
  exact Zw_mul Zw_s2 (hU i j)

lemma res_succ {U : Mat} {k : ℕ} (hU : complexDenominator U k) (i j : Bool) :
    matrixResidue U (k + 1) i j = residueMultiply (bits 10) (matrixResidue U k i j) := by
  unfold matrixResidue
  rw [pow_succ, mul_comm _ ((Real.sqrt 2 : ℝ) : ℂ), mul_assoc, res_mul Zw_s2 (hU i j), res_s2]

lemma mat_res {U : Mat} {k : ℕ} (hU : complexDenominator U k) (A : SmallClifford)
    (hA : ∀ l j, InZomega (A.val l j)) :
    residueAction (matrixResidue U k) A = matrixResidue (U * A.val) k := by
  funext i j
  unfold residueAction matrixResidue
  rw [Matrix.mul_apply, Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [res_sum (fun l => Zw_mul (hU i l) (hA l j))]
  congr 1; funext l; rw [res_mul (hU i l) (hA l j)]

def U4 (r : Residue) : Prop := r = bits 1 ∨ r = bits 2 ∨ r = bits 4 ∨ r = bits 8

def Mono (B : Mat) : Prop := (∀ l j, InZomega (B l j)) ∧
  ((B false true = 0 ∧ B true false = 0 ∧ U4 (residue (B false false)) ∧ U4 (residue (B true true))) ∨
   (B false false = 0 ∧ B true true = 0 ∧ U4 (residue (B false true)) ∧ U4 (residue (B true false))))

lemma U4_mul {c : ℂ} {x : ℂ} (hc : InZomega c) (hx : InZomega x)
    (hrc : residue c = bits 1 ∨ residue c = bits 2 ∨ residue c = bits 4) (h : U4 (residue x)) :
    U4 (residue (c * x)) := by
  rw [res_mul hc hx]
  unfold U4 at *
  rcases hrc with e | e | e <;> rw [e] <;> rcases h with e' | e' | e' | e' <;> rw [e'] <;> decide

lemma mono_scale {B : Mat} (hB : Mono B) (c : Bool → ℂ) (hc : ∀ l, InZomega (c l))
    (hrc : ∀ l, residue (c l) = bits 1 ∨ residue (c l) = bits 2 ∨ residue (c l) = bits 4) :
    Mono (Matrix.of fun l j => c l * B l j) := by
  obtain ⟨hz, h⟩ := hB
  refine ⟨fun l j => Zw_mul (hc l) (hz l j), ?_⟩
  simp only [Matrix.of_apply]
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left; exact ⟨by rw [h1, mul_zero], by rw [h2, mul_zero], U4_mul (hc _) (hz _ _) (hrc _) h3,
      U4_mul (hc _) (hz _ _) (hrc _) h4⟩
  · right; exact ⟨by rw [h1, mul_zero], by rw [h2, mul_zero], U4_mul (hc _) (hz _ _) (hrc _) h3,
      U4_mul (hc _) (hz _ _) (hrc _) h4⟩

lemma S_mul (B : Mat) : QAlgorithms.phaseS * B = Matrix.of fun l j => (if l then Complex.I else 1) * B l j := by
  ext l j; simp [QAlgorithms.phaseS, Matrix.diagonal_mul]

lemma W_mul (B : Mat) : scalarOmega * B = Matrix.of fun l j => (fun _ => ω) l * B l j := by
  ext l j; simp [scalarOmega]

lemma X_mul (B : Mat) : QAlgorithms.pauliX * B = Matrix.of fun l j => B (!l) j := by
  ext l j; cases l <;> simp [QAlgorithms.pauliX, Matrix.mul_apply, Fintype.sum_bool]

lemma mono_one : Mono (1 : Mat) := by
  refine ⟨fun l j => ?_, Or.inl ⟨by simp, by simp, ?_, ?_⟩⟩
  · rw [Matrix.one_apply]; split_ifs; exacts [Zw_one, Zw_zero]
  · simp [res_one, U4]
  · simp [res_one, U4]

lemma mono_gen (B : Mat) (hB : Mono B) (g : SmallLetter) : Mono (smallLetterMatrix g * B) := by
  cases g
  · rw [smallLetterMatrix, S_mul]
    apply mono_scale hB
    · intro l; cases l; exacts [Zw_one, Zw_I]
    · intro l; cases l <;> simp [res_one, res_I]
  · rw [smallLetterMatrix, X_mul]
    obtain ⟨hz, h⟩ := hB
    refine ⟨fun l j => hz _ _, ?_⟩
    simp only [Matrix.of_apply, Bool.not_false, Bool.not_true]
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · right; exact ⟨h2, h1, h4, h3⟩
    · left; exact ⟨h2, h1, h4, h3⟩
  · rw [smallLetterMatrix, W_mul]
    apply mono_scale hB
    · intro l; exact Zw_om
    · intro l; simp [res_om]

lemma mono_word (w : List SmallLetter) : Mono (w.map smallLetterMatrix).prod := by
  induction w with
  | nil => simpa using mono_one
  | cons g w ih => simpa using mono_gen _ ih g

lemma mono_small (A : SmallClifford) : Mono A.val := by
  obtain ⟨B, w, hw⟩ := A
  show Mono B
  rw [← hw]; exact mono_word w

lemma unit_X : QAlgorithms.pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  cases a <;> cases b <;> simp [QAlgorithms.pauliX, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply]

lemma unit_word_small (w : List SmallLetter) :
    (w.map smallLetterMatrix).prod ∈ Matrix.unitaryGroup Bool ℂ := by
  induction w with
  | nil => simpa using (Matrix.unitaryGroup Bool ℂ).one_mem
  | cons g w ih =>
    simp only [List.map_cons, List.prod_cons]
    refine (Matrix.unitaryGroup Bool ℂ).mul_mem ?_ ih
    cases g
    exacts [unit_S, unit_X, unit_W]

lemma unit_small (A : SmallClifford) : A.val ∈ Matrix.unitaryGroup Bool ℂ := by
  obtain ⟨B, w, hw⟩ := A
  show B ∈ _
  rw [← hw]; exact unit_word_small w

lemma small_mul (A B : SmallClifford) : A.val * B.val ∈ smallSet := by
  obtain ⟨_, w, rfl⟩ := A
  obtain ⟨_, v, rfl⟩ := B
  exact ⟨w ++ v, by simp [List.prod_append]⟩

lemma small_word (w : List SmallLetter) : (w.map smallLetterMatrix).prod ∈ smallSet := ⟨w, rfl⟩

end X4P10

-- ===== P10O =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true

def S4 (r : Residue) : Prop := r = bits 2 ∨ r = bits 7 ∨ r = bits 8 ∨ r = bits 13
def T4 (r : Residue) : Prop := r = bits 3 ∨ r = bits 6 ∨ r = bits 9 ∨ r = bits 12

lemma res_expand (x : Residue) : x = ![x 0, x 1, x 2, x 3] := by
  funext i; fin_cases i <;> rfl

lemma F1 (x : Residue) (h : residueMultiply (bits 10) x = bits 5) : S4 x := by
  have key : ∀ a b c d : ZMod 2, residueMultiply (bits 10) ![a, b, c, d] = bits 5 →
      S4 ![a, b, c, d] := by unfold S4; decide
  rw [res_expand x] at h ⊢; exact key _ _ _ _ h

lemma F2 (x u : Residue) (hx : T4 x) (hu : U4 u) : T4 (residueMultiply x u) := by
  unfold T4 U4 at *
  rcases hx with e | e | e | e <;> rw [e] <;> rcases hu with e' | e' | e' | e' <;> rw [e'] <;> decide

lemma F3 (x u : Residue) (hu : U4 u) (h : T4 (residueMultiply x u)) : T4 x := by
  have key : ∀ a b c d : ZMod 2, U4 u → T4 (residueMultiply ![a, b, c, d] u) → T4 ![a, b, c, d] := by
    unfold U4 T4
    rcases hu with e | e | e | e <;> rw [e] <;> decide
  rw [res_expand x] at h ⊢; exact key _ _ _ _ hu h

lemma F4 (x : Residue) (hx : T4 x) : residueMultiply (bits 10) x = bits 15 := by
  unfold T4 at hx
  rcases hx with e | e | e | e <;> rw [e] <;> decide

lemma F5 {x y : Residue} (h : x + y = bits 15) : y = x + bits 15 := by
  rw [← h, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

lemma rM_zero (x : Residue) : residueMultiply x 0 = 0 := by
  funext l; simp [residueMultiply]

lemma act_fwd (R : ResidueMat) (A : SmallClifford) (i j : Bool) :
    ∃ l u, U4 u ∧ residueAction R A i j = residueMultiply (R i l) u := by
  obtain ⟨_, h⟩ := mono_small A
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> cases j
  · exact ⟨false, _, h3, by simp [residueAction, Fintype.sum_bool, h2, res_zero, rM_zero]⟩
  · exact ⟨true, _, h4, by simp [residueAction, Fintype.sum_bool, h1, res_zero, rM_zero]⟩
  · exact ⟨true, _, h4, by simp [residueAction, Fintype.sum_bool, h1, res_zero, rM_zero]⟩
  · exact ⟨false, _, h3, by simp [residueAction, Fintype.sum_bool, h2, res_zero, rM_zero]⟩

lemma act_bwd (R : ResidueMat) (A : SmallClifford) (i l : Bool) :
    ∃ j u, U4 u ∧ residueAction R A i j = residueMultiply (R i l) u := by
  obtain ⟨_, h⟩ := mono_small A
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> cases l
  · exact ⟨false, _, h3, by simp [residueAction, Fintype.sum_bool, h2, res_zero, rM_zero]⟩
  · exact ⟨true, _, h4, by simp [residueAction, Fintype.sum_bool, h1, res_zero, rM_zero]⟩
  · exact ⟨true, _, h3, by simp [residueAction, Fintype.sum_bool, h2, res_zero, rM_zero]⟩
  · exact ⟨false, _, h4, by simp [residueAction, Fintype.sum_bool, h1, res_zero, rM_zero]⟩

lemma act_T (R : ResidueMat) (A : SmallClifford) (h : ∀ i j, T4 (R i j)) (i j : Bool) :
    T4 (residueAction R A i j) := by
  obtain ⟨l, u, hu, e⟩ := act_fwd R A i j
  rw [e]; exact F2 _ _ (h i l) hu

lemma act_T_inv (R : ResidueMat) (A : SmallClifford) (h : ∀ i j, T4 (residueAction R A i j)) (i l : Bool) :
    T4 (R i l) := by
  obtain ⟨j, u, hu, e⟩ := act_bwd R A i l
  exact F3 _ _ hu (e ▸ h i j)

lemma row_norm (V : Mat) (hV : V ∈ Matrix.unitaryGroup Bool ℂ) (i : Bool) :
    Complex.normSq (V i false) + Complex.normSq (V i true) = 1 := by
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hV) i) i
  simp [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Complex.mul_conj] at this
  have h2 := congrArg Complex.re this
  simp at h2
  linarith

lemma forb {V : Mat} (hV : V ∈ Matrix.unitaryGroup Bool ℂ) {k : ℕ} (hk : 2 ≤ k)
    (hd : complexDenominator V k) (i : Bool)
    (h0 : U4 (matrixResidue V k i false)) (h1 : U4 (matrixResidue V k i true)) : False := by
  apply forbidden_unit_vector_residues k hk _ _ (hd i false) (hd i true) h0 h1
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast s2ne)
  rw [mul_div_cancel_left₀ _ hne, mul_div_cancel_left₀ _ hne]
  exact row_norm V hV i

lemma act_of (R : ResidueMat) (A : SmallClifford) (M : ResidueMat)
    (h : ∀ l j, residue (A.val l j) = M l j) :
    residueAction R A = fun i j => ∑ l, residueMultiply (R i l) (M l j) := by
  funext i j; simp only [residueAction, h]

end X4P10

-- ===== P10P =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true

lemma res_om2 : residue (ω * ω) = bits 4 := by
  rw [res_mul Zw_om Zw_om, res_om]; decide

def sw (w : List SmallLetter) : SmallClifford := ⟨(w.map smallLetterMatrix).prod, small_word w⟩


lemma w_nil : ∀ l j, residue ((sw []).val l j) = residueMatrix 1 0 0 1 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_s : ∀ l j, residue ((sw [.s]).val l j) = residueMatrix 1 0 0 4 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_xsx : ∀ l j, residue ((sw [.x, .s, .x]).val l j) = residueMatrix 4 0 0 1 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_ww : ∀ l j, residue ((sw [.omega, .omega]).val l j) = residueMatrix 4 0 0 4 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_x : ∀ l j, residue ((sw [.x]).val l j) = residueMatrix 0 1 1 0 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_xs : ∀ l j, residue ((sw [.x, .s]).val l j) = residueMatrix 0 4 1 0 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_sx : ∀ l j, residue ((sw [.s, .x]).val l j) = residueMatrix 0 1 4 0 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide
lemma w_wwx : ∀ l j, residue ((sw [.omega, .omega, .x]).val l j) = residueMatrix 0 4 4 0 l j := by
  intro l j; cases l <;> cases j <;>
    simp [sw, smallLetterMatrix, QAlgorithms.phaseS, QAlgorithms.pauliX, scalarOmega, residueMatrix,
      Matrix.mul_apply, Fintype.sum_bool, res_one, res_I, res_zero, res_om2] <;> decide

end X4P10

-- ===== P10Q =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

local notation "Mat" => Matrix Bool Bool ℂ
local notation "ω" => QAlgorithms.gateT true true

def pm (p q : Residue) : ResidueMat :=
  fun i j => if i then (if j then q + bits 15 else p + bits 15) else (if j then q else p)

lemma final_case {V : Mat} (hV : V ∈ Matrix.unitaryGroup Bool ℂ) {k : ℕ} (hk : 2 ≤ k)
    (hd : complexDenominator V k) (p q : Residue) (hM : matrixResidue V k = pm p q)
    (hp : S4 p) (hq : S4 q) :
    ∃ B : SmallClifford, residueAction (matrixResidue V k) B = residueMatrix 8 7 7 8 := by
  have f0 := forb hV hk hd false
  have f1 := forb hV hk hd true
  rw [hM] at f0 f1 ⊢
  simp only [pm, if_true, if_false, Bool.false_eq_true] at f0 f1
  unfold S4 at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl
  -- p = 2
  · exact (f0 (by unfold U4; decide) (by unfold U4; decide)).elim
  · exact ⟨sw [.x, .s, .x], by rw [act_of _ _ _ w_xsx]; funext i j; cases i <;> cases j <;> decide⟩
  · exact (f0 (by unfold U4; decide) (by unfold U4; decide)).elim
  · exact ⟨sw [.omega, .omega], by rw [act_of _ _ _ w_ww]; funext i j; cases i <;> cases j <;> decide⟩
  -- p = 7
  · exact ⟨sw [.s, .x], by rw [act_of _ _ _ w_sx]; funext i j; cases i <;> cases j <;> decide⟩
  · exact (f1 (by unfold U4; decide) (by unfold U4; decide)).elim
  · exact ⟨sw [.x], by rw [act_of _ _ _ w_x]; funext i j; cases i <;> cases j <;> decide⟩
  · exact (f1 (by unfold U4; decide) (by unfold U4; decide)).elim
  -- p = 8
  · exact (f0 (by unfold U4; decide) (by unfold U4; decide)).elim
  · exact ⟨sw [], by rw [act_of _ _ _ w_nil]; funext i j; cases i <;> cases j <;> decide⟩
  · exact (f0 (by unfold U4; decide) (by unfold U4; decide)).elim
  · exact ⟨sw [.s], by rw [act_of _ _ _ w_s]; funext i j; cases i <;> cases j <;> decide⟩
  -- p = 13
  · exact ⟨sw [.omega, .omega, .x], by rw [act_of _ _ _ w_wwx]; funext i j; cases i <;> cases j <;> decide⟩
  · exact (f1 (by unfold U4; decide) (by unfold U4; decide)).elim
  · exact ⟨sw [.x, .s], by rw [act_of _ _ _ w_xs]; funext i j; cases i <;> cases j <;> decide⟩
  · exact (f1 (by unfold U4; decide) (by unfold U4; decide)).elim

lemma T_of_eq {R : ResidueMat} (h : R = residueMatrix 3 3 6 6 ∨ R = residueMatrix 3 3 9 9) (i j : Bool) :
    T4 (R i j) := by
  unfold T4
  rcases h with rfl | rfl <;> cases i <;> cases j <;> decide

theorem main (U : Mat) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (k : ℕ) (hk : 2 ≤ k)
    (hdenom : complexDenominator U k)
    (hHdenom : complexDenominator (QAlgorithms.hadamard * U) k)
    (hfirst : residueEquivalent (matrixResidue U (k + 1)) (residueMatrix 5 5 5 5))
    (hsecond : residueEquivalent (matrixResidue (QAlgorithms.hadamard * U) k) (residueMatrix 3 3 6 6) ∨
      residueEquivalent (matrixResidue (QAlgorithms.hadamard * U) k) (residueMatrix 3 3 9 9)) :
    residueEquivalent (matrixResidue U k) (residueMatrix 8 7 7 8) := by
  obtain ⟨A, hA⟩ := hfirst
  have hAz := (mono_small A).1
  have hU' : U * A.val ∈ Matrix.unitaryGroup Bool ℂ := Submonoid.mul_mem _ hU (unit_small A)
  have hd' : complexDenominator (U * A.val) k := denW_mul hdenom hAz
  have hd'' : complexDenominator (QAlgorithms.hadamard * (U * A.val)) k := by
    rw [← mul_assoc]; exact denW_mul hHdenom hAz
  have h5 : ∀ i j, residueMultiply (bits 10) (matrixResidue (U * A.val) k i j) = bits 5 := by
    intro i j
    rw [← res_succ hd', ← mat_res (den_succ hdenom) A hAz, hA]
    cases i <;> cases j <;> rfl
  have hT : ∀ i j, T4 (matrixResidue (QAlgorithms.hadamard * U) k i j) := by
    rcases hsecond with ⟨A', hA'⟩ | ⟨A', hA'⟩
    · exact act_T_inv _ A' (fun i j => by rw [hA']; exact T_of_eq (Or.inl rfl) i j)
    · exact act_T_inv _ A' (fun i j => by rw [hA']; exact T_of_eq (Or.inr rfl) i j)
  have hT' : ∀ i j, T4 (matrixResidue (QAlgorithms.hadamard * (U * A.val)) k i j) := by
    rw [← mul_assoc, ← mat_res hHdenom A hAz]
    exact act_T _ A hT
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast s2ne
  have hsum : ∀ j, matrixResidue (U * A.val) k false j + matrixResidue (U * A.val) k true j = bits 15 := by
    intro j
    have key : ((Real.sqrt 2 : ℝ) : ℂ) ^ k * (U * A.val) false j +
        ((Real.sqrt 2 : ℝ) : ℂ) ^ k * (U * A.val) true j =
        ((Real.sqrt 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) ^ k *
          (QAlgorithms.hadamard * (U * A.val)) false j) := by
      rw [Matrix.mul_apply (M := QAlgorithms.hadamard), Fintype.sum_bool]
      simp only [QAlgorithms.hadamard, Matrix.of_apply, Bool.false_and, Bool.false_eq_true, if_false]
      field_simp
      ring
    unfold matrixResidue
    rw [← res_add (hd' _ _) (hd' _ _), key, res_mul Zw_s2 (hd'' _ _), res_s2]
    exact F4 _ (hT' false j)
  have hM : matrixResidue (U * A.val) k =
      pm (matrixResidue (U * A.val) k false false) (matrixResidue (U * A.val) k false true) := by
    funext i j
    cases i <;> cases j <;> simp only [pm, if_true, if_false, Bool.false_eq_true]
    · exact F5 (hsum false)
    · exact F5 (hsum true)
  obtain ⟨B, hB⟩ := final_case hU' hk hd' _ _ hM (F1 _ (h5 _ _)) (F1 _ (h5 _ _))
  refine ⟨⟨A.val * B.val, small_mul A B⟩, ?_⟩
  rw [mat_res hdenom _ (mono_small ⟨A.val * B.val, small_mul A B⟩).1, ← mul_assoc,
    ← mat_res hd' B (mono_small B).1, hB]

end X4P10

-- ===== P10QSol =====

noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)

open QAlgorithms.QubitChannels (sigma)

local notation "Mat" => Matrix Bool Bool ℂ

local notation "omega" => QAlgorithms.gateT true true

/-- Lemma 7.8, PDF p.9. -/
theorem solution (U : Mat) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (hring : ∀ i j, InDomega (U i j)) (k : ℕ) (hk : 2 ≤ k)
    (hdenom : complexDenominator U k)
    (hHdenom : complexDenominator (QAlgorithms.hadamard * U) k)
    (hfirst : residueEquivalent (matrixResidue U (k + 1)) (residueMatrix 5 5 5 5))
    (hsecond : residueEquivalent (matrixResidue (QAlgorithms.hadamard * U) k) (residueMatrix 3 3 6 6) ∨
      residueEquivalent (matrixResidue (QAlgorithms.hadamard * U) k) (residueMatrix 3 3 9 9)) :
    residueEquivalent (matrixResidue U k) (residueMatrix 8 7 7 8) :=
  X4P10.main U hU k hk hdenom hHdenom hfirst hsecond

end
