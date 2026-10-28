-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.state_preparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:59:17.012759+00:00
-- url     : https://prove2.me/submissions/0b48314f-0d62-4061-8082-006e712a65be

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P13_denominator_changes_attainable


noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)

lemma r2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma r2mul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma s2mul : s2 * s2 = 2 := by
  rw [← Complex.ofReal_mul, r2mul]; norm_num

lemma s2ne : s2 ≠ 0 := by
  have : Real.sqrt 2 ≠ 0 := by positivity
  exact_mod_cast this

lemma s2inv_sq : s2⁻¹ * s2⁻¹ = 1 / 2 := by
  rw [← mul_inv, s2mul]; norm_num

lemma om_eq : ω = ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩ := by
  have h : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  apply Complex.ext <;> simp

lemma om2 : ω ^ 2 = Complex.I := by
  rw [om_eq]; apply Complex.ext <;> simp [pow_two] <;> ring_nf <;> rw [r2sq] <;> norm_num

lemma om4 : ω ^ 4 = -1 := by
  rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, om2, Complex.I_sq]

lemma om8 : ω ^ 8 = 1 := by
  rw [show (8:ℕ) = 4 * 2 from rfl, pow_mul, om4]; norm_num

lemma s2_eq : s2 = ω - ω ^ 3 := by
  rw [pow_succ, om2, om_eq]; apply Complex.ext <;> simp <;> ring

lemma normSq_om : Complex.normSq ω = 1 := by
  rw [om_eq, Complex.normSq_mk]; nlinarith [r2sq]

lemma normSq_om_pow (j : ℕ) : Complex.normSq (ω ^ j) = 1 := by
  rw [map_pow, normSq_om, one_pow]

/-! coordinates (ascending: a0 + a1 ω + a2 ω² + a3 ω³) -/

local notation "cv" => coordinateValue

def mulc (a b : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![a 0 * b 0 - a 1 * b 3 - a 2 * b 2 - a 3 * b 1,
    a 0 * b 1 + a 1 * b 0 - a 2 * b 3 - a 3 * b 2,
    a 0 * b 2 + a 1 * b 1 + a 2 * b 0 - a 3 * b 3,
    a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0]

lemma cv_add (a b : Fin 4 → ℤ) : cv a + cv b = cv (a + b) := by
  simp [coordinateValue]; ring

lemma cv_neg (a : Fin 4 → ℤ) : -cv a = cv (-a) := by
  simp [coordinateValue]; ring

lemma cv_mul (a b : Fin 4 → ℤ) : cv a * cv b = cv (mulc a b) := by
  simp only [coordinateValue, mulc]
  simp
  linear_combination ((a 3 : ℂ) * b 3 * ω ^ 2 + ((a 3 : ℂ) * b 2 + a 2 * b 3) * ω +
    ((a 3 : ℂ) * b 1 + a 2 * b 2 + a 1 * b 3)) * om4

lemma cv_smul (n : ℤ) (a : Fin 4 → ℤ) : (n : ℂ) * cv a = cv (n • a) := by
  simp [coordinateValue]; ring

lemma cv_re (a : Fin 4 → ℤ) :
    (cv a).re = a 0 + (a 1 - a 3) * (Real.sqrt 2 / 2) := by
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, r2sq]
  simp [coordinateValue, om_eq, pow_succ, Complex.mul_re, Complex.mul_im]
  ring_nf; rw [h3]; try rw [r2sq]
  ring

lemma cv_im (a : Fin 4 → ℤ) :
    (cv a).im = a 2 + (a 1 + a 3) * (Real.sqrt 2 / 2) := by
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, r2sq]
  simp [coordinateValue, om_eq, pow_succ, Complex.mul_re, Complex.mul_im]
  ring_nf; rw [h3]; try rw [r2sq]
  ring

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

lemma cv_inj {a b : Fin 4 → ℤ} (h : cv a = cv b) : a = b := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  rw [cv_re, cv_re] at hr
  rw [cv_im, cv_im] at hi
  obtain ⟨r1, r2⟩ := lin_sqrt (2 * (a 0 - b 0)) ((a 1 - a 3) - (b 1 - b 3)) (by push_cast; linarith)
  obtain ⟨i1, i2⟩ := lin_sqrt (2 * (a 2 - b 2)) ((a 1 + a 3) - (b 1 + b 3)) (by push_cast; linarith)
  funext j
  fin_cases j <;> simp <;> omega

lemma normSq_cv (a : Fin 4 → ℤ) :
    Complex.normSq (cv a) = formP a + formQ a * Real.sqrt 2 := by
  rw [Complex.normSq_apply, cv_re, cv_im]
  simp only [formP, formQ]; push_cast
  linear_combination (((a 1 : ℝ) - a 3) ^ 2 + ((a 1 : ℝ) + a 3) ^ 2) / 4 * r2sq

/-! the integral ring is the coordinate range -/

def ZwSub : Subring ℂ where
  carrier := Set.range cv
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨mulc a b, (cv_mul a b).symm⟩
  one_mem' := ⟨![1, 0, 0, 0], by simp [coordinateValue]⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, (cv_add a b).symm⟩
  zero_mem' := ⟨0, by simp [coordinateValue]⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩; exact ⟨-a, (cv_neg a).symm⟩

lemma om_mem : ω ∈ integralRing := Subring.subset_closure (by simp)

lemma cv_mem (a : Fin 4 → ℤ) : cv a ∈ integralRing := by
  have h : ∀ n : ℤ, (n : ℂ) ∈ integralRing := fun n => intCast_mem _ n
  unfold coordinateValue
  refine add_mem (add_mem (add_mem (h _) (mul_mem (h _) om_mem))
    (mul_mem (h _) (pow_mem om_mem _))) (mul_mem (h _) (pow_mem om_mem _))

lemma mem_iff (x : ℂ) : x ∈ integralRing ↔ ∃ a, cv a = x := by
  constructor
  · intro hx
    have : integralRing ≤ ZwSub := by
      unfold integralRing
      rw [Subring.closure_le]
      rintro _ rfl
      exact ⟨![0, 1, 0, 0], by simp [coordinateValue]⟩
    exact this hx
  · rintro ⟨a, rfl⟩; exact cv_mem a

lemma s2_mem : s2 ∈ integralRing := by
  rw [s2_eq]; exact sub_mem om_mem (pow_mem om_mem _)

lemma I_mem : Complex.I ∈ integralRing := by
  rw [← om2]; exact pow_mem om_mem _

/-- halving: if all coordinates are even, cv a / 2 is integral. -/
lemma half_mem (a : Fin 4 → ℤ) (h : ∀ i, 2 ∣ a i) : cv a / 2 ∈ integralRing := by
  choose q hq using h
  rw [mem_iff]
  refine ⟨q, ?_⟩
  simp only [coordinateValue, hq]; push_cast; ring

lemma mem_half {a : Fin 4 → ℤ} (h : cv a / 2 ∈ integralRing) : ∀ i, 2 ∣ a i := by
  obtain ⟨q, hq⟩ := (mem_iff _).1 h
  have : cv a = cv ((2 : ℤ) • q) := by rw [← cv_smul, hq]; push_cast; ring
  have := cv_inj this
  intro i; exact ⟨q i, by rw [this]; simp⟩

end X4P13

noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)

/-! reachability of first columns -/

def Reach (z w : ℂ) : Prop :=
  ∃ c : List HTLetter, htWordMatrix c false false = z ∧ htWordMatrix c true false = w

lemma word_snoc (c : List HTLetter) (l : HTLetter) :
    htWordMatrix (c ++ [l]) = htMatrix l * htWordMatrix c := by
  simp [htWordMatrix]

lemma reach_nil : Reach 1 0 := ⟨[], by simp [htWordMatrix]⟩

lemma reach_T {z w : ℂ} (h : Reach z w) : Reach z (ω * w) := by
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨c ++ [.t], ?_, ?_⟩ <;>
    simp [word_snoc, htMatrix, Matrix.mul_apply, QAlgorithms.gateT, h1, h2]

lemma reach_H {z w : ℂ} (h : Reach z w) : Reach (s2⁻¹ * (z + w)) (s2⁻¹ * (z - w)) := by
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨c ++ [.h], ?_, ?_⟩ <;>
    simp [word_snoc, htMatrix, Matrix.mul_apply, QAlgorithms.hadamard, h1, h2] <;> ring

lemma reach_Tpow {z w : ℂ} (h : Reach z w) (n : ℕ) : Reach z (ω ^ n * w) := by
  induction n with
  | zero => simpa using h
  | succ n ih => have := reach_T ih; rwa [← mul_assoc, ← pow_succ'] at this

lemma reach_swap {z w : ℂ} (h : Reach z w) : Reach w z := by
  have h1 := reach_H (reach_Tpow (reach_H h) 4)
  rw [om4] at h1
  convert h1 using 1
  · linear_combination (-2 * w) * s2inv_sq
  · linear_combination (-2 * z) * s2inv_sq

end X4P13

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
local notation "cv" => coordinateValue

lemma reach_phase {z w : ℂ} (h : Reach z w) : Reach (ω * z) (ω * w) :=
  reach_swap (reach_T (reach_swap (reach_T h)))

lemma reach_unit0 (m : ℕ) : Reach (ω ^ m) 0 := by
  induction m with
  | zero => simpa using reach_nil
  | succ m ih => have := reach_phase ih; rwa [mul_zero, ← pow_succ'] at this

lemma reach_step {z w : ℂ} (j : ℕ)
    (h : Reach (s2⁻¹ * (z + ω ^ j * w)) (s2⁻¹ * (z - ω ^ j * w))) : Reach z w := by
  have h1 := reach_Tpow (reach_H h) (7 * j)
  convert h1 using 1
  · linear_combination (-2 * z) * s2inv_sq
  · have : ω ^ (7 * j) * ω ^ j = 1 := by
      rw [← pow_add, show 7 * j + j = 8 * j by ring, pow_mul, om8, one_pow]
    linear_combination (-(ω ^ (7 * j)) * 2 * ω ^ j * w) * s2inv_sq - w * this

lemma om_pow_add4 (j : ℕ) : ω ^ (j + 4) = -ω ^ j := by
  rw [pow_add, om4]; ring

lemma unit_of_P1 (a : Fin 4 → ℤ) (hP : formP a = 1) : ∃ m : ℕ, cv a = ω ^ m := by
  unfold formP at hP
  have b0 : -1 ≤ a 0 ∧ a 0 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
  have b1 : -1 ≤ a 1 ∧ a 1 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 2), sq_nonneg (a 3)]
  have b2 : -1 ≤ a 2 ∧ a 2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a 1), sq_nonneg (a 0), sq_nonneg (a 3)]
  have b3 : -1 ≤ a 3 ∧ a 3 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 0)]
  obtain h0|h0|h0 : a 0 = -1 ∨ a 0 = 0 ∨ a 0 = 1 := by omega
  all_goals obtain h1|h1|h1 : a 1 = -1 ∨ a 1 = 0 ∨ a 1 = 1 := by omega
  all_goals obtain h2|h2|h2 : a 2 = -1 ∨ a 2 = 0 ∨ a 2 = 1 := by omega
  all_goals obtain h3|h3|h3 : a 3 = -1 ∨ a 3 = 0 ∨ a 3 = 1 := by omega
  all_goals rw [h0, h1, h2, h3] at hP; norm_num at hP
  all_goals simp only [coordinateValue, h0, h1, h2, h3]; push_cast
  all_goals first
    | (refine ⟨0, ?_⟩; ring1) | (refine ⟨1, ?_⟩; ring1) | (refine ⟨2, ?_⟩; ring1) | (refine ⟨3, ?_⟩; ring1)
    | (refine ⟨4, ?_⟩; rw [show (4:ℕ) = 0 + 4 from rfl, om_pow_add4]; ring1)
    | (refine ⟨5, ?_⟩; rw [show (5:ℕ) = 1 + 4 from rfl, om_pow_add4]; ring1)
    | (refine ⟨6, ?_⟩; rw [show (6:ℕ) = 2 + 4 from rfl, om_pow_add4]; ring1)
    | (refine ⟨7, ?_⟩; rw [show (7:ℕ) = 3 + 4 from rfl, om_pow_add4]; ring1)

lemma zero_of_P0 (a : Fin 4 → ℤ) (hP : formP a = 0) : cv a = 0 := by
  unfold formP at hP
  have h0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
  have h1 : a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
  have h2 : a 2 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
  have h3 : a 3 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
  simp [coordinateValue, h0, h1, h2, h3]

lemma P_nonneg (a : Fin 4 → ℤ) : 0 ≤ formP a := by unfold formP; positivity

lemma norm_eq_PQ {a b : Fin 4 → ℤ} {n : ℕ}
    (h : Complex.normSq (cv a) + Complex.normSq (cv b) = 2 ^ n) :
    formP a + formP b = 2 ^ n ∧ formQ a + formQ b = 0 := by
  rw [normSq_cv, normSq_cv] at h
  have := lin_sqrt (formP a + formP b - 2 ^ n) (formQ a + formQ b) (by push_cast; linarith)
  omega

lemma base0 {a b : Fin 4 → ℤ}
    (h : Complex.normSq (cv a) + Complex.normSq (cv b) = 1) : Reach (cv a) (cv b) := by
  obtain ⟨hP, -⟩ := norm_eq_PQ (n := 0) (by simpa using h)
  have pa := P_nonneg a; have pb := P_nonneg b
  rcases (show formP a = 0 ∨ formP b = 0 by omega) with ha | hb
  · obtain ⟨m, hm⟩ := unit_of_P1 b (by omega)
    rw [zero_of_P0 a ha, hm]; exact reach_swap (reach_unit0 m)
  · obtain ⟨m, hm⟩ := unit_of_P1 a (by omega)
    rw [zero_of_P0 b hb, hm]; exact reach_unit0 m

end X4P13

noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
local notation "cv" => coordinateValue

/-! finite residue checks -/

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma fin_step : ∀ r0 < 2, ∀ r1 < 2, ∀ r2 < 2, ∀ r3 < 2, ∀ t0 < 2, ∀ t1 < 2, ∀ t2 < 2, ∀ t3 < 2,
    ¬ ((r1 + r3) % 2 = 0 ∧ (r0 + r2) % 2 = 0 ∧ (t1 + t3) % 2 = 0 ∧ (t0 + t2) % 2 = 0) →
    ((r0 + r2) * (r1 + r3) + (t0 + t2) * (t1 + t3)) % 2 = 0 →
    ((r0 + r1 + r2 + r3 + t0 + t1 + t2 + t3) % 4 = 2 ∨
      ((r0 + r1 + r2 + r3) % 2 = 0 ∧ (t0 + t1 + t2 + t3) % 2 = 0 ∧
        (r0 + r1 + r2 + r3 + t0 + t1 + t2 + t3) % 4 = 0)) →
    ((r0 + t0) % 2 = 0 ∧ (r1 + t1) % 2 = 0 ∧ (r2 + t2) % 2 = 0 ∧ (r3 + t3) % 2 = 0) ∨
    ((r0 + t3) % 2 = 0 ∧ (r1 + t0) % 2 = 0 ∧ (r2 + t1) % 2 = 0 ∧ (r3 + t2) % 2 = 0) ∨
    ((r0 + t2) % 2 = 0 ∧ (r1 + t3) % 2 = 0 ∧ (r2 + t0) % 2 = 0 ∧ (r3 + t1) % 2 = 0) ∨
    ((r0 + t1) % 2 = 0 ∧ (r1 + t2) % 2 = 0 ∧ (r2 + t3) % 2 = 0 ∧ (r3 + t0) % 2 = 0) := by
  decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
lemma fin_k3 : ∀ r0 < 2, ∀ r1 < 2, ∀ r2 < 2, ∀ r3 < 2,
    ¬ ((r1 + r3) % 2 = 0 ∧ (r0 + r2) % 2 = 0) →
    (r0 + r1 + r2 + r3) % 2 = 1 ∨ ((r0 + r2) * (r1 + r3)) % 2 = 1 := by
  decide +kernel

/-- the parity bit of an integer, as a natural number -/
def bt (x : ℤ) : ℕ := (x % 2).toNat

lemma bt_eq (x : ℤ) : ((bt x : ℕ) : ℤ) = x % 2 := by
  unfold bt; have := Int.emod_two_eq_zero_or_one x; omega

lemma bt_lt (x : ℤ) : bt x < 2 := by
  unfold bt; have := Int.emod_two_eq_zero_or_one x; omega

lemma bit_mem (x : ℤ) : x % 2 ∈ ({0, 1} : Finset ℤ) := by
  rcases Int.emod_two_eq_zero_or_one x with h | h <;> simp [h]

lemma sq_mod4 (x : ℤ) : x ^ 2 ≡ x % 2 [ZMOD 4] := by
  obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' x
  · rw [Int.modEq_iff_dvd]; exact ⟨-q ^ 2, by rw [Int.mul_emod_right]; ring⟩
  · rw [Int.modEq_iff_dvd]
    refine ⟨-(q ^ 2 + q), ?_⟩
    have : (2 * q + 1) % 2 = 1 := by omega
    rw [this]; ring

lemma P_mod4 (a : Fin 4 → ℤ) :
    formP a ≡ a 0 % 2 + a 1 % 2 + a 2 % 2 + a 3 % 2 [ZMOD 4] :=
  (((sq_mod4 _).add (sq_mod4 _)).add (sq_mod4 _)).add (sq_mod4 _)

lemma Q_mod2 (a : Fin 4 → ℤ) :
    formQ a ≡ (a 0 % 2 + a 2 % 2) * (a 1 % 2 + a 3 % 2) [ZMOD 2] := by
  have e : ∀ i, a i ≡ a i % 2 [ZMOD 2] := fun i => (Int.mod_modEq _ _).symm
  have h1 : formQ a ≡ (a 0 + a 2) * (a 1 + a 3) [ZMOD 2] := by
    rw [Int.modEq_iff_dvd]; exact ⟨a 0 * a 3, by unfold formQ; ring⟩
  exact h1.trans (((e 0).add (e 2)).mul ((e 1).add (e 3)))

def rot (b : Fin 4 → ℤ) : Fin 4 → ℤ := ![-b 3, b 0, b 1, b 2]

lemma cv_rot1 (b : Fin 4 → ℤ) : cv ![-b 3, b 0, b 1, b 2] = ω ^ 1 * cv b := by
  simp [coordinateValue]; linear_combination (-(b 3 : ℂ)) * om4

lemma cv_rot2 (b : Fin 4 → ℤ) : cv ![-b 2, -b 3, b 0, b 1] = ω ^ 2 * cv b := by
  simp [coordinateValue]; linear_combination (-((b 2 : ℂ) + b 3 * ω)) * om4

lemma cv_rot3 (b : Fin 4 → ℤ) : cv ![-b 1, -b 2, -b 3, b 0] = ω ^ 3 * cv b := by
  simp [coordinateValue]; linear_combination (-((b 1 : ℂ) + b 2 * ω + b 3 * ω ^ 2)) * om4

def Div2 (a : Fin 4 → ℤ) : Prop := 2 ∣ a 1 - a 3 ∧ 2 ∣ a 0 - a 2

lemma nd_bits (a b : Fin 4 → ℤ) (hnd : ¬ (Div2 a ∧ Div2 b)) :
    ¬ ((bt (a 1) + bt (a 3)) % 2 = 0 ∧ (bt (a 0) + bt (a 2)) % 2 = 0 ∧
      (bt (b 1) + bt (b 3)) % 2 = 0 ∧ (bt (b 0) + bt (b 2)) % 2 = 0) := by
  have e0 := bt_eq (a 0); have e1 := bt_eq (a 1); have e2 := bt_eq (a 2); have e3 := bt_eq (a 3)
  have f0 := bt_eq (b 0); have f1 := bt_eq (b 1); have f2 := bt_eq (b 2); have f3 := bt_eq (b 3)
  rintro ⟨h1, h2, h3, h4⟩
  apply hnd
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

lemma P_bits (a b : Fin 4 → ℤ)
    (hP : (formP a + formP b) % 4 = 2 ∨
      (formP a % 2 = 0 ∧ formP b % 2 = 0 ∧ (formP a + formP b) % 4 = 0)) :
    ((bt (a 0) + bt (a 1) + bt (a 2) + bt (a 3) + bt (b 0) + bt (b 1) + bt (b 2) + bt (b 3)) % 4 = 2 ∨
      ((bt (a 0) + bt (a 1) + bt (a 2) + bt (a 3)) % 2 = 0 ∧
        (bt (b 0) + bt (b 1) + bt (b 2) + bt (b 3)) % 2 = 0 ∧
        (bt (a 0) + bt (a 1) + bt (a 2) + bt (a 3) + bt (b 0) + bt (b 1) + bt (b 2) + bt (b 3)) % 4 = 0)) := by
  have pa := P_mod4 a; have pb := P_mod4 b
  unfold Int.ModEq at pa pb
  simp only [← bt_eq] at pa pb
  generalize formP a = A at *
  generalize formP b = B at *
  generalize bt (a 0) = x0 at *
  generalize bt (a 1) = x1 at *
  generalize bt (a 2) = x2 at *
  generalize bt (a 3) = x3 at *
  generalize bt (b 0) = y0 at *
  generalize bt (b 1) = y1 at *
  generalize bt (b 2) = y2 at *
  generalize bt (b 3) = y3 at *
  omega

lemma Q_bits (a b : Fin 4 → ℤ) (hQ : formQ a + formQ b = 0) :
    ((bt (a 0) + bt (a 2)) * (bt (a 1) + bt (a 3)) +
      (bt (b 0) + bt (b 2)) * (bt (b 1) + bt (b 3))) % 2 = 0 := by
  have qa := Q_mod2 a; have qb := Q_mod2 b
  unfold Int.ModEq at qa qb
  have hQ' : ((a 0 % 2 + a 2 % 2) * (a 1 % 2 + a 3 % 2) +
      (b 0 % 2 + b 2 % 2) * (b 1 % 2 + b 3 % 2)) % 2 = 0 := by
    rw [Int.add_emod, ← qa, ← qb, ← Int.add_emod, hQ]; rfl
  rw [← bt_eq (a 0), ← bt_eq (a 1), ← bt_eq (a 2), ← bt_eq (a 3)] at hQ'
  rw [← bt_eq (b 0), ← bt_eq (b 1), ← bt_eq (b 2), ← bt_eq (b 3)] at hQ'
  exact_mod_cast hQ'

lemma concl_bits {x y : ℤ} (h : (bt x + bt y) % 2 = 0) : 2 ∣ x + y ∧ 2 ∣ x + -y := by
  have := bt_eq x; have := bt_eq y; omega

lemma step_choice (a b : Fin 4 → ℤ) (hnd : ¬ (Div2 a ∧ Div2 b))
    (hQ : formQ a + formQ b = 0)
    (hP : (formP a + formP b) % 4 = 2 ∨
      (formP a % 2 = 0 ∧ formP b % 2 = 0 ∧ (formP a + formP b) % 4 = 0)) :
    ∃ j : ℕ, ∃ c : Fin 4 → ℤ, cv c = ω ^ j * cv b ∧ ∀ i, 2 ∣ a i + c i := by
  have := fin_step _ (bt_lt (a 0)) _ (bt_lt (a 1)) _ (bt_lt (a 2)) _ (bt_lt (a 3))
    _ (bt_lt (b 0)) _ (bt_lt (b 1)) _ (bt_lt (b 2)) _ (bt_lt (b 3))
    (nd_bits a b hnd) (Q_bits a b hQ) (P_bits a b hP)
  rcases this with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · refine ⟨0, b, by simp, fun i => ?_⟩
    fin_cases i
    exacts [(concl_bits h0).1, (concl_bits h1).1, (concl_bits h2).1, (concl_bits h3).1]
  · refine ⟨1, _, cv_rot1 b, fun i => ?_⟩
    fin_cases i
    exacts [(concl_bits h0).2, (concl_bits h1).1, (concl_bits h2).1, (concl_bits h3).1]
  · refine ⟨2, _, cv_rot2 b, fun i => ?_⟩
    fin_cases i
    exacts [(concl_bits h0).2, (concl_bits h1).2, (concl_bits h2).1, (concl_bits h3).1]
  · refine ⟨3, _, cv_rot3 b, fun i => ?_⟩
    fin_cases i
    exacts [(concl_bits h0).2, (concl_bits h1).2, (concl_bits h2).2, (concl_bits h3).1]

lemma not_div2 (a : Fin 4 → ℤ) (h : ¬ Div2 a) : ¬ (2 ∣ formP a ∧ 2 ∣ formQ a) := by
  have pa := P_mod4 a; have qa := Q_mod2 a
  unfold Int.ModEq at pa qa
  rw [← bt_eq (a 0), ← bt_eq (a 1), ← bt_eq (a 2), ← bt_eq (a 3)] at pa qa
  have e0 := bt_eq (a 0); have e1 := bt_eq (a 1); have e2 := bt_eq (a 2); have e3 := bt_eq (a 3)
  have := fin_k3 _ (bt_lt (a 0)) _ (bt_lt (a 1)) _ (bt_lt (a 2)) _ (bt_lt (a 3))
    (by unfold Div2 at h; omega)
  rcases this with h1 | h1
  · omega
  · have h2 : (((bt (a 0) + bt (a 2)) * (bt (a 1) + bt (a 3)) : ℕ) : ℤ) % 2 = 1 := by
      exact_mod_cast h1
    push_cast at h2
    omega

end X4P13

noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
local notation "cv" => coordinateValue
local notation "Zw" => integralRing

lemma s2_pow_two_mul (n : ℕ) : s2 ^ (2 * n) = 2 ^ n := by
  rw [pow_mul, sq, s2mul]

lemma normSq_s2 : Complex.normSq s2 = 2 := by
  rw [Complex.normSq_ofReal, r2mul]

lemma normSquared_scale {z : ℂ} {n : ℕ} {a : Fin 4 → ℤ} (h : s2 ^ n * z = cv a) :
    ((Complex.normSq (cv a) : ℝ) : ℂ) = s2 ^ (2 * n) * normSquared z := by
  rw [← h, map_mul, map_pow, normSq_s2, s2_pow_two_mul, normSquared]; push_cast; ring

lemma PQ_mem (a : Fin 4 → ℤ) :
    ((Complex.normSq (cv a) : ℝ) : ℂ) = cv ![formP a, formQ a, 0, -formQ a] := by
  rw [normSq_cv]; push_cast
  simp only [coordinateValue]; simp
  rw [s2_eq]; ring

lemma s2inv_eq : s2⁻¹ = cv ![0, 1, 0, -1] / 2 := by
  have : cv ![0, 1, 0, -1] = s2 := by rw [s2_eq]; simp [coordinateValue]; ring
  rw [this]; field_simp [s2ne]; rw [sq, s2mul]

lemma s2inv_half : s2⁻¹ = s2 / 2 := by
  field_simp [s2ne]; rw [sq, s2mul]

lemma div_s2_mem {a : Fin 4 → ℤ} (h : Div2 a) : s2⁻¹ * cv a ∈ Zw := by
  rw [s2inv_eq, div_mul_eq_mul_div, cv_mul]
  apply half_mem
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
  intro i; fin_cases i <;> simp [mulc]
  · exact ⟨p, by linarith⟩
  · exact ⟨q + a 2, by linarith⟩
  · exact ⟨p + a 3, by linarith⟩
  · exact ⟨-q, by linarith⟩

lemma inv_small {z : ℂ} {k : ℕ} (hk : k ≤ 1) (h : s2 ^ k * z ∈ Zw) :
    s2 ^ 3 * normSquared z ∈ Zw := by
  obtain ⟨a, ha⟩ := (mem_iff _).1 h
  have e := normSquared_scale ha.symm
  rw [PQ_mem] at e
  have : s2 ^ 3 * normSquared z = s2 ^ (3 - 2 * k) * (s2 ^ (2 * k) * normSquared z) := by
    rw [← mul_assoc, ← pow_add, show 3 - 2 * k + 2 * k = 3 by omega]
  rw [this, ← e]
  exact mul_mem (pow_mem s2_mem _) (cv_mem _)

lemma normSq_inv_s2 : Complex.normSq s2⁻¹ = 1 / 2 := by
  rw [map_inv₀, normSq_s2]; norm_num

lemma unit_step {z w : ℂ} (j : ℕ) (h : Complex.normSq z + Complex.normSq w = 1) :
    Complex.normSq (s2⁻¹ * (z + ω ^ j * w)) + Complex.normSq (s2⁻¹ * (z - ω ^ j * w)) = 1 := by
  rw [map_mul, map_mul, normSq_inv_s2, Complex.normSq_add, Complex.normSq_sub, map_mul,
    normSq_om_pow]
  linarith

/-- the small-denominator base: entries with √2-exponent k and |z|², |w|² of sde ≤ 3. -/
lemma base (k : ℕ) : ∀ z w : ℂ, Complex.normSq z + Complex.normSq w = 1 →
    s2 ^ k * z ∈ Zw → s2 ^ k * w ∈ Zw →
    s2 ^ 3 * normSquared z ∈ Zw → s2 ^ 3 * normSquared w ∈ Zw → Reach z w := by
  induction k with
  | zero =>
    intro z w hu hz hw _ _
    obtain ⟨a, ha⟩ := (mem_iff _).1 hz
    obtain ⟨b, hb⟩ := (mem_iff _).1 hw
    simp only [pow_zero, one_mul] at ha hb
    rw [← ha, ← hb] at hu ⊢
    exact base0 hu
  | succ k ih =>
    intro z w hu hz hw iz iw
    obtain ⟨a, ha⟩ := (mem_iff _).1 hz
    obtain ⟨b, hb⟩ := (mem_iff _).1 hw
    have na := normSquared_scale ha.symm
    have nb := normSquared_scale hb.symm
    have hnorm : Complex.normSq (cv a) + Complex.normSq (cv b) = 2 ^ (k + 1) := by
      have : ((Complex.normSq (cv a) + Complex.normSq (cv b) : ℝ) : ℂ) = ((2 ^ (k + 1) : ℝ) : ℂ) := by
        push_cast; rw [na, nb, normSquared, normSquared, s2_pow_two_mul, ← mul_add]
        rw [← Complex.ofReal_add, hu]; push_cast; ring
      exact_mod_cast this
    obtain ⟨hP, hQ⟩ := norm_eq_PQ hnorm
    by_cases hd : Div2 a ∧ Div2 b
    · apply ih z w hu _ _ iz iw
      · have : s2 ^ k * z = s2⁻¹ * cv a := by
          rw [ha, pow_succ]; field_simp [s2ne]
        rw [this]; exact div_s2_mem hd.1
      · have : s2 ^ k * w = s2⁻¹ * cv b := by
          rw [hb, pow_succ]; field_simp [s2ne]
        rw [this]; exact div_s2_mem hd.2
    · -- parity facts from the invariant
      have key : ∀ (c : Fin 4 → ℤ) (u : ℂ), s2 ^ (k + 1) * u = cv c →
          s2 ^ 3 * normSquared u ∈ Zw →
          (k = 1 → 2 ∣ formP c) ∧ (2 ≤ k → 2 ∣ formP c ∧ 2 ∣ formQ c) := by
        intro c u hc iu
        have nc := normSquared_scale hc
        rw [PQ_mem] at nc
        refine ⟨fun hk1 => ?_, fun hk2 => ?_⟩
        · subst hk1
          -- s2^3 |u|^2 = (P + Q s2)/s2 = P s2⁻¹ + Q
          have e1 : s2 ^ 3 * normSquared u = s2⁻¹ * cv ![formP c, formQ c, 0, -formQ c] := by
            rw [nc]; field_simp [s2ne]; ring
          have e2 : s2⁻¹ * cv ![formP c, formQ c, 0, -formQ c] =
              cv ![0, formP c, 0, -formP c] / 2 + (formQ c : ℂ) := by
            rw [s2inv_eq, div_mul_eq_mul_div, cv_mul]
            simp [coordinateValue, mulc]; ring
          have hm : cv ![0, formP c, 0, -formP c] / 2 ∈ Zw := by
            have := sub_mem (e1 ▸ iu : s2⁻¹ * cv ![formP c, formQ c, 0, -formQ c] ∈ Zw)
              (intCast_mem Zw (formQ c))
            rwa [e2, add_sub_cancel_right] at this
          simpa using mem_half hm 1
        · have e1 : cv ![formP c, formQ c, 0, -formQ c] =
              2 * (s2 ^ (2 * k - 3) * (s2 ^ 3 * normSquared u)) := by
            rw [nc, show 2 * (k + 1) = 2 + (2 * k - 3 + 3) by omega, pow_add, pow_add, sq, s2mul]
            ring
          have hm : cv ![formP c, formQ c, 0, -formQ c] / 2 ∈ Zw := by
            rw [e1, mul_div_cancel_left₀ _ two_ne_zero]
            exact mul_mem (pow_mem s2_mem _) iu
          have := mem_half hm
          exact ⟨by simpa using this 0, by simpa using this 1⟩
      have ka := key a z ha.symm iz
      have kb := key b w hb.symm iw
      have hk : k ≤ 1 := by
        by_contra hk
        rcases not_and_or.1 hd with h | h
        · exact not_div2 a h (ka.2 (by omega))
        · exact not_div2 b h (kb.2 (by omega))
      have hP' : (formP a + formP b) % 4 = 2 ∨
          (formP a % 2 = 0 ∧ formP b % 2 = 0 ∧ (formP a + formP b) % 4 = 0) := by
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
        · left; rw [hP]; norm_num
        · right; have := ka.1 rfl; have := kb.1 rfl; rw [hP]; omega
      obtain ⟨j, c, hc, hdiv⟩ := step_choice a b hd hQ hP'
      apply reach_step j
      have hsum : s2 ^ k * (s2⁻¹ * (z + ω ^ j * w)) = cv (a + c) / 2 := by
        rw [← cv_add, hc, ha, hb, s2inv_half]; ring
      have hz' : s2 ^ k * (s2⁻¹ * (z + ω ^ j * w)) ∈ Zw := by
        rw [hsum]; exact half_mem _ hdiv
      have hw' : s2 ^ k * (s2⁻¹ * (z - ω ^ j * w)) ∈ Zw := by
        have : s2 ^ k * (s2⁻¹ * (z - ω ^ j * w)) =
            s2 ^ k * (s2⁻¹ * (z + ω ^ j * w)) - cv c := by
          rw [hsum, ← cv_add, hc, hb, ha, s2inv_half]; ring
        rw [this]; exact sub_mem hz' (cv_mem c)
      exact ih _ _ (unit_step j hu) hz' hw' (inv_small hk hz') (inv_small hk hw')

end X4P13

noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
local notation "cv" => coordinateValue
local notation "Zw" => integralRing

lemma s2inv_syn : s2⁻¹ ∈ synthesisRing := Subring.subset_closure (by simp)
lemma I_syn : Complex.I ∈ synthesisRing := Subring.subset_closure (by simp)

lemma om_syn : ω ∈ synthesisRing := by
  have : ω = (1 + Complex.I) * s2⁻¹ := by
    rw [om_eq]; field_simp [s2ne]
    apply Complex.ext <;> simp <;> nlinarith [r2sq]
  rw [this]; exact mul_mem (add_mem (one_mem _) I_syn) s2inv_syn

def DenSub : Subring ℂ where
  carrier := {z | ∃ k : ℕ, s2 ^ k * z ∈ Zw}
  mul_mem' := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have : s2 ^ (k + l) * (x * y) = (s2 ^ k * x) * (s2 ^ l * y) := by ring
    rw [this]; exact mul_mem hk hl
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have : s2 ^ (k + l) * (x + y) = s2 ^ l * (s2 ^ k * x) + s2 ^ k * (s2 ^ l * y) := by ring
    rw [this]; exact add_mem (mul_mem (pow_mem s2_mem _) hk) (mul_mem (pow_mem s2_mem _) hl)
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨k, hk⟩; exact ⟨k, by rw [mul_neg]; exact neg_mem hk⟩

lemma ring_den {z : ℂ} (hz : z ∈ synthesisRing) : ∃ k : ℕ, s2 ^ k * z ∈ Zw := by
  have : synthesisRing ≤ DenSub := by
    unfold synthesisRing; rw [Subring.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ s2ne]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact I_mem⟩
  exact this hz

lemma ring_den2 {z w : ℂ} (hz : z ∈ synthesisRing) (hw : w ∈ synthesisRing) :
    ∃ k : ℕ, s2 ^ k * z ∈ Zw ∧ s2 ^ k * w ∈ Zw := by
  obtain ⟨k, hk⟩ := ring_den hz
  obtain ⟨l, hl⟩ := ring_den hw
  refine ⟨k + l, ?_, ?_⟩
  · rw [pow_add, mul_comm (s2 ^ k), mul_assoc]; exact mul_mem (pow_mem s2_mem _) hk
  · rw [pow_add, mul_assoc]; exact mul_mem (pow_mem s2_mem _) hl

lemma normSquared_mem {z : ℂ} (hz : z ∈ synthesisRing) :
    ∃ m : ℕ, normSquared z * s2 ^ m ∈ Zw := by
  obtain ⟨k, hk⟩ := ring_den hz
  obtain ⟨a, ha⟩ := (mem_iff _).1 hk
  refine ⟨2 * k, ?_⟩
  rw [mul_comm, ← normSquared_scale ha.symm, PQ_mem]; exact cv_mem _

lemma main_ind (m : ℕ) : ∀ z w : ℂ, z ∈ synthesisRing → w ∈ synthesisRing →
    Complex.normSq z + Complex.normSq w = 1 → normSquared z * s2 ^ m ∈ Zw → Reach z w := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro z w hz hw hu hm
  obtain ⟨K, hKz, hKw⟩ := ring_den2 hz hw
  by_cases B : s2 ^ 3 * normSquared z ∈ Zw
  · refine base K z w hu hKz hKw B ?_
    have : s2 ^ 3 * normSquared w = s2 ^ 3 - s2 ^ 3 * normSquared z := by
      have hu' : normSquared z + normSquared w = 1 := by
        simp only [normSquared]; exact_mod_cast hu
      rw [show normSquared w = 1 - normSquared z by linear_combination hu']; ring
    rw [this]; exact sub_mem (pow_mem s2_mem _) B
  · have hex : ∃ n : ℕ, normSquared z * s2 ^ n ∈ Zw := ⟨m, hm⟩
    set n0 := Nat.find hex with hn0
    have hspec : normSquared z * s2 ^ n0 ∈ Zw := Nat.find_spec hex
    have hle : n0 ≤ m := Nat.find_min' hex hm
    have h3 : 3 < n0 := by
      by_contra h
      apply B
      have : s2 ^ 3 * normSquared z = s2 ^ (3 - n0) * (normSquared z * s2 ^ n0) := by
        rw [mul_comm (normSquared z), ← mul_assoc, ← pow_add, show 3 - n0 + n0 = 3 by omega]
      rw [this]; exact mul_mem (pow_mem s2_mem _) hspec
    have hsde : IsSDE (normSquared z) (n0 : ℤ) := by
      refine ⟨by rw [zpow_natCast]; exact hspec, fun e he => ?_⟩
      rcases le_or_gt 0 e with he0 | he0
      · obtain ⟨e', rfl⟩ := Int.eq_ofNat_of_zero_le he0
        rw [zpow_natCast] at he
        have := Nat.find_min' hex he; rw [← hn0] at this; exact_mod_cast this
      · exfalso
        have h0 : normSquared z * s2 ^ (0 : ℕ) ∈ Zw := by
          obtain ⟨e', he'⟩ := Int.exists_eq_neg_ofNat he0.le
          have : normSquared z * s2 ^ (0 : ℕ) = (normSquared z * s2 ^ e) * s2 ^ e' := by
            rw [mul_assoc, ← zpow_natCast s2 e', ← zpow_add₀ s2ne, he']; simp
          rw [this]; exact mul_mem he (pow_mem s2_mem _)
        have := Nat.find_min' hex h0
        omega
    obtain ⟨j, hj⟩ := denominator_changes_attainable z w hz hw hu (n0 : ℤ) hsde
      (by exact_mod_cast h3) (-1) (Or.inl rfl)
    apply reach_step j.val
    have ez : (z + w * ω ^ j.val) / s2 = s2⁻¹ * (z + ω ^ j.val * w) := by ring
    rw [ez] at hj
    have hz' : s2⁻¹ * (z + ω ^ j.val * w) ∈ synthesisRing :=
      mul_mem s2inv_syn (add_mem hz (mul_mem (pow_mem om_syn _) hw))
    have hw' : s2⁻¹ * (z - ω ^ j.val * w) ∈ synthesisRing :=
      mul_mem s2inv_syn (sub_mem hz (mul_mem (pow_mem om_syn _) hw))
    refine ih (n0 - 1) (by omega) _ _ hz' hw' (unit_step j.val hu) ?_
    have := hj.1
    rwa [show (n0 : ℤ) + -1 = ((n0 - 1 : ℕ) : ℤ) by omega, zpow_natCast] at this

end X4P13

open QAlgorithms.Papers.Independent.Support21.P13 in
open scoped Classical in
theorem solution (psi : EuclideanSpace ℂ Bool)
    (hstate : QAlgorithms.IsState psi) (hring : ∀ b, psi b ∈ synthesisRing) :
    ∃ c : List HTLetter, QAlgorithms.act (htWordMatrix c) (QAlgorithms.ket false) = psi := by
  have hu : Complex.normSq (psi false) + Complex.normSq (psi true) = 1 := by
    have h := hstate
    unfold QAlgorithms.IsState at h
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_bool] at h
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; linarith
  obtain ⟨m, hm⟩ := X4P13.normSquared_mem (hring false)
  obtain ⟨c, h1, h2⟩ := X4P13.main_ind m _ _ (hring false) (hring true) hu hm
  refine ⟨c, ?_⟩
  ext b
  cases b <;> simp [QAlgorithms.act, QAlgorithms.ket, 
    Fintype.sum_bool, h1, h2]

