-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.ma_bloch_parity_and_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:23:54.236275+00:00
-- url     : https://prove2.me/submissions/07c51be1-db36-4f90-94c4-54c178637c87

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_column_coefficient_identities
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_row_coefficient_identities
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_bloch_clifford_characterization

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

-- ===== P10J =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)
open scoped Classical BigOperators

lemma lde_shape (W : RealMat) (n : ℕ) (hn : 1 ≤ n) (r c : Fin 3) (hd : realDenominator W n)
    (hp : ∀ i j, matrixParity W n i j = shape r c i j) :
    realLde W = n ∧ parityEquivalent (matrixParity W (realLde W)) (parityPattern r) := by
  have hl : realLde W = n := by
    apply lde_of_odd W n hn hd
    refine ⟨r, c + 1, ?_⟩
    rw [hp]
    fin_cases r <;> fin_cases c <;> decide
  refine ⟨hl, Equiv.swap 2 c, fun i j => ?_⟩
  rw [hl, hp, shape_pattern]

/-- Data computed from the syntax. -/
theorem core (M : NormalForm) :
    (M.leadingT = false ∧ M.body = [] ∧ realLde (operatorBloch (maValue M)) = 0 ∧ maValue M ∈ cliffordSet) ∨
    (realLde (operatorBloch (maValue M)) = normalTCount M ∧ 0 < normalTCount M ∧
      ∃ r : Fin 3, parityEquivalent (matrixParity (operatorBloch (maValue M))
        (realLde (operatorBloch (maValue M)))) (parityPattern r) ∧
        ((M.leadingT = true ∧ r = 0) ∨ (M.leadingT = false ∧ M.body.head? = some false ∧ r = 1) ∨
          (M.leadingT = false ∧ M.body.head? = some true ∧ r = 2))) := by
  obtain ⟨lt, body, C⟩ := M
  have hv := maValue_eq ⟨lt, body, C⟩
  obtain ⟨hd, ⟨c, hc⟩, hsh⟩ := inv body C
  cases lt
  · replace hv : maValue ⟨false, body, C⟩ = R body C := by rw [hv]; simp
    rw [hv]
    cases body with
    | nil =>
      left
      rw [R_nil]
      refine ⟨rfl, rfl, ?_, C.property⟩
      show realLde (operatorBloch C.val) = 0
      have := lde_min _ (by simpa [R_nil] using hd)
      omega
    | cons q rest =>
      right
      obtain ⟨c', hc'⟩ := hsh q rest rfl
      obtain ⟨hl, hpe⟩ := lde_shape _ _ (by simp) _ c' hd hc'
      refine ⟨?_, ?_, (if q then 2 else 1), hpe, ?_⟩
      · rw [hl]; simp only [normalTCount, List.length_cons]; simp
      · simp only [normalTCount, List.length_cons]; simp
      · cases q <;> simp
  · replace hv : maValue ⟨true, body, C⟩ = QAlgorithms.gateT * R body C := by rw [hv]; simp
    right
    have hB : operatorBloch (maValue ⟨true, body, C⟩) = BL 0 * operatorBloch (R body C) := by
      rw [hv, bloch_mul _ _ (unit_R body C), bloch_T]; rfl
    obtain ⟨hd', hp'⟩ := step 0 _ _ hd
    have hshape : ∀ i j, matrixParity (operatorBloch (maValue ⟨true, body, C⟩)) (body.length + 1) i j =
        shape 0 c i j := by
      intro i j
      rw [hB, hp', hc]
      fin_cases i <;> by_cases hj : j = c <;> simp [shape, hj]
    rw [← hB] at hd'
    obtain ⟨hl, hpe⟩ := lde_shape _ _ (by simp) 0 c hd' hshape
    refine ⟨?_, ?_, 0, hpe, ?_⟩
    · rw [hl]; simp only [normalTCount]; simp [add_comm]
    · simp only [normalTCount]; simp
    · simp

lemma cnt_cliff (C : Clifford) : (expandClifford C).countP (fun a => decide (a = Letter.t)) = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  unfold expandClifford at ha
  rw [List.mem_map] at ha
  obtain ⟨x, -, rfl⟩ := ha
  cases x <;> simp

lemma letter_count (M : NormalForm) :
    letterTCount (normalWord cliffordH cliffordSH M) = normalTCount M := by
  obtain ⟨lt, body, C⟩ := M
  unfold letterTCount normalWord
  rw [← List.countP_eq_length_filter, List.countP_flatMap, List.map_reverse, List.sum_reverse]
  simp only [normalTokens, normalTCount, List.map_append, List.sum_append]
  have hb : (List.map ((List.countP fun a => decide (a = Letter.t)) ∘ expandToken)
      (body.flatMap fun q => [Token.clifford (if q then cliffordSH else cliffordH), Token.t])).sum =
      body.length := by
    induction body with
    | nil => simp
    | cons q rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.length_cons]
      simp [expandToken, cnt_cliff]
      ring
  rw [hb]
  cases lt <;> simp [expandToken, cnt_cliff] <;> ring

theorem lemma410 (M : NormalForm) :
    (∃! tag : Fin 4, blochCase M tag) ∧
    normalTCount M = realLde (operatorBloch (maValue M)) ∧
    letterTCount (normalWord cliffordH cliffordSH M) = realLde (operatorBloch (maValue M)) := by
  have hcount : normalTCount M = realLde (operatorBloch (maValue M)) := by
    rcases core M with ⟨h1, h2, h3, -⟩ | ⟨h1, -⟩
    · rw [h3]; simp [normalTCount, h1, h2]
    · exact h1.symm
  refine ⟨?_, hcount, by rw [letter_count, hcount]⟩
  rcases core M with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, r, hpe, hr⟩
  · refine ⟨0, by simp [blochCase, h3, h4], fun t ht => ?_⟩
    fin_cases t
    · rfl
    all_goals simp [blochCase, h3] at ht
  · rw [h1] at hpe
    rcases hr with ⟨hl, rfl⟩ | ⟨hl, hh, rfl⟩ | ⟨hl, hh, rfl⟩
    · refine ⟨1, by simp [blochCase, hpe, hl, h1, h2], fun t ht => ?_⟩
      fin_cases t <;> simp [blochCase, hl, h1] at ht ⊢
      all_goals omega
    · refine ⟨2, by simp [blochCase, hpe, hl, hh, h1, h2], fun t ht => ?_⟩
      fin_cases t <;> simp [blochCase, hl, hh, h1] at ht ⊢
      all_goals omega
    · refine ⟨3, by simp [blochCase, hpe, hl, hh, h1, h2], fun t ht => ?_⟩
      fin_cases t <;> simp [blochCase, hl, hh, h1] at ht ⊢
      all_goals omega

end X4P10

-- ===== P10JSol =====

noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

/-- Lemma 4.10, PDF pp.4-5. -/
theorem solution (M : NormalForm) :
    (∃! tag : Fin 4, blochCase M tag) ∧
    normalTCount M = realLde (operatorBloch (maValue M)) ∧
    letterTCount (normalWord cliffordH cliffordSH M) = realLde (operatorBloch (maValue M)) :=
  X4P10.lemma410 M

end
