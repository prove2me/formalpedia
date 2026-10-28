-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.so3_exact_denominator_lowering
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:06:43.074973+00:00
-- url     : https://prove2.me/submissions/c7794460-9cf8-45a0-adff-be0010b67f2d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_column_coefficient_identities
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_row_coefficient_identities

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

-- ===== P10F =====

noncomputable section

namespace X4P10

open QAlgorithms.Papers.Independent.Gap48.P10
open scoped Classical BigOperators

section
variable (U : RealMat) (A B : Matrix (Fin 3) (Fin 3) ℤ) (k : ℕ) (hk : 1 ≤ k)
  (hAB : ∀ i j, U i j = ((A i j : ℝ) + (B i j : ℝ) * Real.sqrt 2) / (Real.sqrt 2) ^ k)
include hk hAB

lemma den_r0 (ha : ∀ j, (A 0 j : ZMod 2) = A 1 j) (hb : ∀ j, (B 0 j : ZMod 2) = B 1 j)
    (hx : ∀ j, (A 2 j : ZMod 2) = 0) : realDenominator (BT.transpose * U) (k - 1) := by
  intro i j
  fin_cases i
  · exact low_pair k hk (U 0 j) (U 1 j) _ _ _ _ _ 1 1 (hAB 0 j) (hAB 1 j) (Or.inl rfl) (Or.inl rfl)
      (ha j) (hb j) (by simp [BT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
  · exact low_pair k hk (U 0 j) (U 1 j) _ _ _ _ _ (-1) 1 (hAB 0 j) (hAB 1 j) (Or.inr rfl) (Or.inl rfl)
      (ha j) (hb j) (by simp [BT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
  · exact low_single k hk (U 2 j) _ _ _ 1 (hAB 2 j) (hx j)
      (by simp [BT, Matrix.mul_apply, Fin.sum_univ_three])

lemma den_r1 (ha : ∀ j, (A 1 j : ZMod 2) = A 2 j) (hb : ∀ j, (B 1 j : ZMod 2) = B 2 j)
    (hx : ∀ j, (A 0 j : ZMod 2) = 0) : realDenominator (BHT.transpose * U) (k - 1) := by
  intro i j
  fin_cases i
  · exact low_pair k hk (U 1 j) (U 2 j) _ _ _ _ _ (-1) 1 (hAB 1 j) (hAB 2 j) (Or.inr rfl) (Or.inl rfl)
      (ha j) (hb j) (by simp [BHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
  · exact low_pair k hk (U 1 j) (U 2 j) _ _ _ _ _ (-1) (-1) (hAB 1 j) (hAB 2 j) (Or.inr rfl) (Or.inr rfl)
      (ha j) (hb j) (by simp [BHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
  · exact low_single k hk (U 0 j) _ _ _ 1 (hAB 0 j) (hx j)
      (by simp [BHT, Matrix.mul_apply, Fin.sum_univ_three])

lemma den_r2 (ha : ∀ j, (A 2 j : ZMod 2) = A 0 j) (hb : ∀ j, (B 2 j : ZMod 2) = B 0 j)
    (hx : ∀ j, (A 1 j : ZMod 2) = 0) : realDenominator (BSHT.transpose * U) (k - 1) := by
  intro i j
  fin_cases i
  · exact low_pair k hk (U 2 j) (U 0 j) _ _ _ _ _ 1 1 (hAB 2 j) (hAB 0 j) (Or.inl rfl) (Or.inl rfl)
      (ha j) (hb j) (by simp [BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
  · exact low_pair k hk (U 2 j) (U 0 j) _ _ _ _ _ (-1) 1 (hAB 2 j) (hAB 0 j) (Or.inr rfl) (Or.inl rfl)
      (ha j) (hb j) (by simp [BSHT, Matrix.mul_apply, Fin.sum_univ_three]; ring)
  · exact low_single k hk (U 1 j) _ _ _ 1 (hAB 1 j) (hx j)
      (by simp [BSHT, Matrix.mul_apply, Fin.sum_univ_three])

end

lemma finish (U L : RealMat) (hL : ∀ a b, InZsqrt2 (Real.sqrt 2 * L a b)) (hO : L * L.transpose = 1)
    (hk : 0 < realLde U) (hd : realDenominator (L.transpose * U) (realLde U - 1)) :
    realLde (L.transpose * U) = realLde U - 1 :=
  lde_eq _ hd (fun j hj => by have := lower_bound L U hL hO hj; omega)

theorem lemma64 (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (hk : 0 < realLde U) :
    ∃ r : Fin 3,
      realLde ((operatorBloch (leftSyllable r)).transpose * U) = realLde U - 1 := by
  obtain ⟨A, B, hAB, r, c, hsh, hB⟩ := struct U hU hring hk
  have hk1 : 1 ≤ realLde U := hk
  have hr0 : r ≠ r + 2 := by fin_cases r <;> decide
  have hr1 : r + 1 ≠ r + 2 := by fin_cases r <;> decide
  have hA : ∀ j, (A r j : ZMod 2) = A (r + 1) j := by
    intro j; rw [hsh, hsh]; simp [shape, hr0, hr1]
  have hx : ∀ j, (A (r + 2) j : ZMod 2) = 0 := by
    intro j; rw [hsh]; simp [shape]
  refine ⟨r, ?_⟩
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
  · have e : leftSyllable 0 = QAlgorithms.gateT := by simp [leftSyllable]
    rw [e, bloch_T]
    exact finish U BT hL_T orth_T hk (den_r0 U A B _ hk1 hAB hA hB hx)
  · have e : leftSyllable 1 = QAlgorithms.hadamard * QAlgorithms.gateT := by simp [leftSyllable]
    rw [e, bloch_HT]
    exact finish U BHT hL_HT orth_HT hk (den_r1 U A B _ hk1 hAB hA hB hx)
  · have e : leftSyllable 2 = QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.gateT := by
      simp [leftSyllable]
    rw [e, bloch_SHT]
    exact finish U BSHT hL_SHT orth_SHT hk (den_r2 U A B _ hk1 hAB hA hB hx)

end X4P10

-- ===== P10FSol =====

noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

/-- Lemma 6.4, PDF pp.6-7. -/
theorem solution (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) (hk : 0 < realLde U) :
    ∃ r : Fin 3,
      realLde ((operatorBloch (leftSyllable r)).transpose * U) = realLde U - 1 :=
  X4P10.lemma64 U hU hring hk

end
