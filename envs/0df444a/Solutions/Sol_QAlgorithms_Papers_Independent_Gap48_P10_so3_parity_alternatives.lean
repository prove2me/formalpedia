-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P10.so3_parity_alternatives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:58:20.453305+00:00
-- url     : https://prove2.me/submissions/fc5a0a2a-60ae-4291-ab07-1fc1d0814d64

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P10_bloch_clifford_characterization
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

-- ===== P10CSol =====

noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

/-- Lemma 6.3, PDF p.6. -/
theorem solution (U : RealMat) (hU : SpecialOrthogonal U)
    (hring : ∀ i j, InDsqrt2 (U i j)) :
    (realLde U = 0 → ∃ C : Clifford, operatorBloch C.val = U) ∧
    (0 < realLde U → ∃ r : Fin 3,
      parityEquivalent (matrixParity U (realLde U)) (parityPattern r)) :=
  X4P10.lemma63 U hU hring

end
