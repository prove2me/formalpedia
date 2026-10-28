-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.algorithm1_correct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:17:56.761984+00:00
-- url     : https://prove2.me/submissions/e0f701f3-3657-4bf6-b9f0-d2b8dd43e671

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P13_denominator_changes_attainable
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P13_exact_synthesis_iff
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P13_state_unitary_reduction


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


noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
local notation "cv" => coordinateValue
local notation "Zw" => integralRing

/-! ## the height-≤3 set is finite -/

lemma unit_scale {z w : ℂ} {k : ℕ} {a b : Fin 4 → ℤ} (hu : Complex.normSq z + Complex.normSq w = 1)
    (ha : cv a = s2 ^ k * z) (hb : cv b = s2 ^ k * w) :
    Complex.normSq (cv a) + Complex.normSq (cv b) = 2 ^ k := by
  rw [ha, hb, map_mul, map_mul, map_pow, normSq_s2, ← mul_add, hu, mul_one]

lemma key2 {k : ℕ} (hk : 2 ≤ k) {c : Fin 4 → ℤ} {u : ℂ} (hc : s2 ^ (k + 1) * u = cv c)
    (iu : s2 ^ 3 * normSquared u ∈ Zw) : 2 ∣ formP c ∧ 2 ∣ formQ c := by
  have nc := normSquared_scale hc
  rw [PQ_mem] at nc
  have e1 : cv ![formP c, formQ c, 0, -formQ c] =
      2 * (s2 ^ (2 * k - 3) * (s2 ^ 3 * normSquared u)) := by
    rw [nc, show 2 * (k + 1) = 2 + (2 * k - 3 + 3) by omega, pow_add, pow_add, sq, s2mul]
    ring
  have hm : cv ![formP c, formQ c, 0, -formQ c] / 2 ∈ Zw := by
    rw [e1, mul_div_cancel_left₀ _ two_ne_zero]
    exact mul_mem (pow_mem s2_mem _) iu
  have := mem_half hm
  exact ⟨by simpa using this 0, by simpa using this 1⟩

lemma red2 (k : ℕ) : ∀ z w : ℂ, Complex.normSq z + Complex.normSq w = 1 →
    s2 ^ k * z ∈ Zw → s2 ^ k * w ∈ Zw →
    s2 ^ 3 * normSquared z ∈ Zw → s2 ^ 3 * normSquared w ∈ Zw →
    s2 ^ 2 * z ∈ Zw ∧ s2 ^ 2 * w ∈ Zw := by
  induction k with
  | zero =>
    intro z w _ hz hw _ _
    simp only [pow_zero, one_mul] at hz hw
    exact ⟨mul_mem (pow_mem s2_mem _) hz, mul_mem (pow_mem s2_mem _) hw⟩
  | succ k ih =>
    intro z w hu hz hw iz iw
    by_cases hk : k + 1 ≤ 2
    · have e : ∀ x : ℂ, s2 ^ 2 * x = s2 ^ (2 - (k + 1)) * (s2 ^ (k + 1) * x) := by
        intro x; rw [← mul_assoc, ← pow_add, show 2 - (k + 1) + (k + 1) = 2 by omega]
      rw [e z, e w]
      exact ⟨mul_mem (pow_mem s2_mem _) hz, mul_mem (pow_mem s2_mem _) hw⟩
    obtain ⟨a, ha⟩ := (mem_iff _).1 hz
    obtain ⟨b, hb⟩ := (mem_iff _).1 hw
    by_cases hd : Div2 a ∧ Div2 b
    · apply ih z w hu _ _ iz iw
      · have : s2 ^ k * z = s2⁻¹ * cv a := by
          rw [ha, pow_succ]; field_simp [s2ne]
        rw [this]; exact div_s2_mem hd.1
      · have : s2 ^ k * w = s2⁻¹ * cv b := by
          rw [hb, pow_succ]; field_simp [s2ne]
        rw [this]; exact div_s2_mem hd.2
    · exfalso
      rcases not_and_or.1 hd with h | h
      · exact not_div2 a h (key2 (by omega) ha.symm iz)
      · exact not_div2 b h (key2 (by omega) hb.symm iw)

def Fset : Set ℂ := (fun a => cv a / 2) '' (Set.univ.pi fun _ => Set.Icc (-2 : ℤ) 2)

lemma Fset_finite : Fset.Finite :=
  (Set.Finite.pi (fun _ => Set.finite_Icc (-2 : ℤ) 2)).image _

lemma mem_Fset {z w : ℂ} (hu : Complex.normSq z + Complex.normSq w = 1)
    (hz : s2 ^ 2 * z ∈ Zw) (hw : s2 ^ 2 * w ∈ Zw) : z ∈ Fset := by
  obtain ⟨a, ha⟩ := (mem_iff _).1 hz
  obtain ⟨b, hb⟩ := (mem_iff _).1 hw
  obtain ⟨hP, -⟩ := norm_eq_PQ (unit_scale hu ha hb)
  have pb := P_nonneg b
  have hPa : formP a ≤ 4 := by norm_num at hP; omega
  unfold formP at hPa
  refine ⟨a, fun i _ => ?_, ?_⟩
  · fin_cases i <;> simp <;> constructor <;>
      nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
  · simp only; rw [ha, sq, s2mul]; field_simp

/-! valuations -/

lemma sde_unique {x : ℂ} {d e : ℤ} (hd : IsSDE x d) (he : IsSDE x e) : d = e :=
  le_antisymm (hd.2 e he.1) (he.2 d hd.1)

lemma finiteExponent_eq {x : ℂ} {d : ℤ} (hd : IsSDE x d) : finiteExponent x = d := by
  have hex : ∃ d, IsSDE x d := ⟨d, hd⟩
  unfold finiteExponent; rw [dif_pos hex]
  exact sde_unique (Classical.choose_spec hex) hd

lemma two_pow_dvd_zero (x : ℤ) (h : ∀ n : ℕ, (2 : ℤ) ^ n ∣ x) : x = 0 := by
  by_contra hx
  have hd : 2 ^ x.natAbs ∣ x.natAbs := by
    have := Int.natAbs_dvd_natAbs.2 (h x.natAbs); simpa [Int.natAbs_pow] using this
  exact absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hx) hd) (not_le.2 Nat.lt_two_pow_self)

lemma sde_exists {x : ℂ} (hx : x ≠ 0) {e0 : ℕ} (h0 : x * s2 ^ e0 ∈ Zw) : ∃ d, IsSDE x d := by
  obtain ⟨a, ha⟩ := (mem_iff _).1 h0
  have hup : ∀ e : ℤ, x * s2 ^ e ∈ Zw → ∀ m : ℕ, x * s2 ^ (e + m) ∈ Zw := by
    intro e he m
    rw [zpow_add₀ s2ne, ← mul_assoc, zpow_natCast]; exact mul_mem he (pow_mem s2_mem _)
  have hbdd : ∃ b : ℤ, ∀ e, x * s2 ^ e ∈ Zw → b ≤ e := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hz : ∀ i, a i = 0 := by
      intro i
      apply two_pow_dvd_zero
      intro n
      obtain ⟨e, he, hlt⟩ := hcon ((e0 : ℤ) - 2 * n)
      have hm := hup e he ((e0 : ℤ) - 2 * n - e).toNat
      rw [show e + (((e0 : ℤ) - 2 * n - e).toNat : ℤ) = (e0 : ℤ) - 2 * n by omega] at hm
      obtain ⟨q, hq⟩ := (mem_iff _).1 hm
      have : cv a = cv ((2 : ℤ) ^ n • q) := by
        have : (((2 : ℤ) ^ n : ℤ) : ℂ) = s2 ^ ((2 * n : ℕ) : ℤ) := by
          rw [zpow_natCast, s2_pow_two_mul]; push_cast; rfl
        rw [← cv_smul, hq, ha, this, ← zpow_natCast s2 e0, mul_left_comm, ← zpow_add₀ s2ne]
        congr 2; push_cast; ring
      have := congrFun (cv_inj this) i
      exact ⟨q i, by rw [this]; simp⟩
    have : a = 0 := funext hz
    rw [this] at ha
    have hs : s2 ^ e0 ≠ 0 := pow_ne_zero _ s2ne
    have : x * s2 ^ e0 = 0 := by rw [← ha]; simp [coordinateValue]
    exact (mul_eq_zero.1 this).resolve_right hs
  obtain ⟨b, hb⟩ := hbdd
  obtain ⟨d, hd, hmin⟩ := Int.exists_least_of_bdd ⟨b, hb⟩ ⟨(e0 : ℤ), by rwa [zpow_natCast]⟩
  exact ⟨d, hd, hmin⟩

lemma normSquared_ne {z : ℂ} (hz : z ≠ 0) : normSquared z ≠ 0 := by
  unfold normSquared; exact_mod_cast (Complex.normSq_pos.2 hz).ne'

lemma ne_of_sde {z : ℂ} {d : ℤ} (h : IsSDE (normSquared z) d) : z ≠ 0 := by
  rintro rfl
  obtain ⟨_, hmin⟩ := h
  have := hmin (d - 1) (by simp [normSquared])
  omega

lemma sde_of_ring {z : ℂ} (hz : z ∈ synthesisRing) (h0 : z ≠ 0) : ∃ d, IsSDE (normSquared z) d := by
  obtain ⟨m, hm⟩ := normSquared_mem hz
  exact sde_exists (normSquared_ne h0) hm

lemma height_eq {U : Matrix Bool Bool ℂ} {d : ℤ} (h : IsSDE (normSquared (U false false)) d) :
    matrixHeight U = d.toNat := by
  unfold matrixHeight; rw [if_neg (ne_of_sde h), finiteExponent_eq h]

lemma inv_of_height {U : Matrix Bool Bool ℂ} (hz : U false false ∈ synthesisRing)
    (hh : matrixHeight U ≤ 3) : s2 ^ 3 * normSquared (U false false) ∈ Zw := by
  by_cases h0 : U false false = 0
  · rw [h0]; simp [normSquared]
  obtain ⟨d, hd⟩ := sde_of_ring hz h0
  rw [height_eq hd] at hh
  have : s2 ^ 3 * normSquared (U false false) =
      s2 ^ (3 - d).toNat * (normSquared (U false false) * s2 ^ d) := by
    rw [mul_comm (normSquared _) (s2 ^ d), ← mul_assoc, ← zpow_natCast s2 (3 - d).toNat,
      ← zpow_add₀ s2ne,
      show (((3 - d).toNat : ℕ) : ℤ) + d = ((3 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [this]; exact mul_mem (pow_mem s2_mem _) hd.1

lemma col_unit {U : Matrix Bool Bool ℂ} (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    Complex.normSq (U false false) + Complex.normSq (U true false) = 1 := by
  have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hU) false) false
  rw [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.star_apply,
    Matrix.one_apply_eq] at h1
  have h1' : ((Complex.normSq (U false false) + Complex.normSq (U true false) : ℝ) : ℂ) = 1 := by
    push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self, add_comm]
    exact h1
  exact_mod_cast h1'

lemma low_finite : {U : Matrix Bool Bool ℂ | U ∈ Matrix.unitaryGroup Bool ℂ ∧ EntriesInRing U ∧
    matrixHeight U ≤ 3}.Finite := by
  refine ((Fset_finite.prod (Fset_finite.prod (Set.finite_univ (α := Fin 8)))).image
    (fun p : ℂ × ℂ × Fin 8 => phaseCompletion p.1 p.2.1 (p.2.2.val : ℤ))).subset ?_
  rintro U ⟨hU, hring, hh⟩
  obtain ⟨c, hc⟩ := (exact_synthesis_iff U hU).1 hring
  obtain ⟨k, -, hk, -⟩ := state_unitary_reduction U hU hring c (fun b => by rw [hc])
  have hu := col_unit hU
  have hu' : Complex.normSq (U true false) + Complex.normSq (U false false) = 1 := by linarith
  obtain ⟨K, hKz, hKw⟩ := ring_den2 (hring false false) (hring true false)
  have iz := inv_of_height (hring false false) hh
  have iw : s2 ^ 3 * normSquared (U true false) ∈ Zw := by
    have e : s2 ^ 3 * normSquared (U true false) =
        s2 ^ 3 - s2 ^ 3 * normSquared (U false false) := by
      have : normSquared (U false false) + normSquared (U true false) = 1 := by
        simp only [normSquared]; exact_mod_cast hu
      rw [show normSquared (U true false) = 1 - normSquared (U false false) by
        linear_combination this]; ring
    rw [e]; exact sub_mem (pow_mem s2_mem _) iz
  obtain ⟨h2z, h2w⟩ := red2 K _ _ hu hKz hKw iz iw
  exact ⟨(U false false, U true false, k), ⟨mem_Fset hu h2z h2w, mem_Fset hu' h2w h2z, trivial⟩,
    hk.symm⟩

end X4P13

noncomputable section

namespace X4P13

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "ω" => QAlgorithms.gateT true true
local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)
local notation "cv" => coordinateValue
local notation "Zw" => integralRing
local notation "Mat" => Matrix Bool Bool ℂ

/-! ## gates -/

lemma T_diag : QAlgorithms.gateT = Matrix.diagonal (fun a => if a then ω else 1) := by
  ext i j; cases i <;> cases j <;> rfl

lemma T_pow (k : ℕ) : QAlgorithms.gateT ^ k = Matrix.diagonal (fun a => if a then ω ^ k else 1) := by
  rw [T_diag, Matrix.diagonal_pow]; congr 1; funext a; cases a <;> simp

lemma star_om : star ω = ω ^ 7 := by
  rw [show (7:ℕ) = 3 + 4 from rfl, om_pow_add4, pow_succ, om2, om_eq]
  apply Complex.ext <;> simp

lemma star_T_pow (k : ℕ) : star (QAlgorithms.gateT ^ k) = QAlgorithms.gateT ^ (7 * k) := by
  rw [T_pow, T_pow, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1; funext a; cases a <;> simp [star_pow, star_om, ← pow_mul]

lemma T_pow_mul (k : ℕ) : QAlgorithms.gateT ^ k * QAlgorithms.gateT ^ (7 * k) = 1 := by
  rw [← pow_add, T_pow, ← Matrix.diagonal_one]; congr 1; funext a; cases a <;> simp
  rw [show k + 7 * k = 8 * k by ring, pow_mul, om8, one_pow]

lemma had_star : star QAlgorithms.hadamard = QAlgorithms.hadamard := by
  ext i j; cases i <;> cases j <;>
    simp [QAlgorithms.hadamard, Matrix.star_apply, Complex.conj_ofReal]

lemma had_sq : QAlgorithms.hadamard * QAlgorithms.hadamard = 1 := by
  ext i j
  cases i <;> cases j <;> simp [QAlgorithms.hadamard, Matrix.mul_apply, Fintype.sum_bool] <;>
    first | (rw [← mul_inv, ← Complex.ofReal_mul, r2mul]; norm_num) | ring

lemma had_unitary : QAlgorithms.hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', had_star, had_sq]

lemma Tpow_unitary (k : ℕ) : QAlgorithms.gateT ^ (7 * k) ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_T_pow, ← pow_add, T_pow, ← Matrix.diagonal_one]
  congr 1; funext a; cases a <;> simp
  rw [show 7 * (7 * k) + 7 * k = 8 * (7 * k) by ring, pow_mul, om8, one_pow]

lemma red_eq (U : Mat) (k : ℕ) :
    reduction U k = QAlgorithms.hadamard * QAlgorithms.gateT ^ (7 * k) * U := by
  rw [reduction, star_T_pow]

lemma red_unitary {U : Mat} (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (k : ℕ) :
    reduction U k ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [red_eq]; exact mul_mem (mul_mem had_unitary (Tpow_unitary k)) hU

lemma mul_ring {A B : Mat} (hA : EntriesInRing A) (hB : EntriesInRing B) :
    EntriesInRing (A * B) := by
  intro a b
  rw [Matrix.mul_apply, Fintype.sum_bool]
  exact add_mem (mul_mem (hA _ _) (hB _ _)) (mul_mem (hA _ _) (hB _ _))

lemma had_ring : EntriesInRing QAlgorithms.hadamard := by
  intro a b
  simp only [QAlgorithms.hadamard, Matrix.of_apply]
  split_ifs
  · exact neg_mem (by simpa using s2inv_syn)
  · simpa using s2inv_syn

lemma Tpow_ring (k : ℕ) : EntriesInRing (QAlgorithms.gateT ^ k) := by
  intro a b
  rw [T_pow, Matrix.diagonal_apply]
  split_ifs <;> first | exact zero_mem _ | exact one_mem _ | exact pow_mem om_syn _

lemma red_ring {U : Mat} (hU : EntriesInRing U) (k : ℕ) : EntriesInRing (reduction U k) := by
  rw [red_eq]; exact mul_ring (mul_ring had_ring (Tpow_ring _)) hU

lemma red_entry (U : Mat) (k : ℕ) :
    reduction U k false false = s2⁻¹ * (U false false + ω ^ (7 * k) * U true false) := by
  rw [red_eq, T_pow]
  simp [Matrix.mul_apply, Fintype.sum_bool, QAlgorithms.hadamard, Matrix.diagonal_apply]
  ring

/-! ## words and BFS -/

lemma word_append (c d : List HTLetter) : htWordMatrix (c ++ d) = htWordMatrix d * htWordMatrix c := by
  simp [htWordMatrix]

lemma word_rep (k : ℕ) : htWordMatrix (List.replicate k .t) = QAlgorithms.gateT ^ k := by
  simp [htWordMatrix, htMatrix, List.map_replicate, List.reverse_replicate, List.prod_replicate]

lemma mem_wordsAt (c : List HTLetter) : c ∈ wordsAt c.length := by
  induction c using List.reverseRecOn with
  | nil => simp [wordsAt]
  | append_singleton c l ih =>
    rw [List.length_append, List.length_singleton, wordsAt, List.mem_flatMap]
    exact ⟨c, ih, by cases l <;> simp⟩

lemma find_spec {U : Mat} {n : ℕ}
    (h : ((wordsAt n).find? fun c => decide (htWordMatrix c = U)).isSome = true) :
    htWordMatrix (((wordsAt n).find? fun c => decide (htWordMatrix c = U)).getD []) = U := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  rw [hc]
  have := List.find?_some hc
  simpa using this

lemma base_spec (U : Mat) (hw : ∃ c, htWordMatrix c = U) :
    ((wordsAt (baseDepth U)).find? fun c => decide (htWordMatrix c = U)).isSome = true ∧
      htWordMatrix (baseWord U) = U := by
  obtain ⟨c, hc⟩ := hw
  have hex : ∃ n : ℕ, ∃ c ∈ wordsAt n, htWordMatrix c = U := ⟨c.length, c, mem_wordsAt c, hc⟩
  have hbd : baseDepth U = Nat.find hex := by unfold baseDepth; rw [dif_pos hex]
  obtain ⟨c', hc', hcU⟩ := Nat.find_spec hex
  rw [← hbd] at hc'
  have hs : ((wordsAt (baseDepth U)).find? fun c => decide (htWordMatrix c = U)).isSome = true :=
    List.find?_isSome.2 ⟨c', hc', by simp [hcU]⟩
  exact ⟨hs, find_spec hs⟩

lemma trace_sound {B : ℕ} {U : Mat} {c : List HTLetter} (h : SynthesisTrace B U c) :
    htWordMatrix c = U := by
  induction h with
  | base low depth hit => exact find_spec hit
  | @step U k c high choice next ih =>
    rw [word_append, word_append, word_rep, ih, red_eq]
    simp only [htWordMatrix, htMatrix, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    simp only [← mul_assoc]
    rw [mul_assoc (QAlgorithms.gateT ^ k) QAlgorithms.hadamard QAlgorithms.hadamard, had_sq,
      mul_one, T_pow_mul, one_mul]

/-! ## algorithm unfolding -/

lemma alg_low {U : Mat} (h : matrixHeight U ≤ 3) : algorithm1 U = baseWord U := by
  unfold algorithm1
  rcases hn : matrixHeight U with _ | f
  · rfl
  · simp only [synthesisFuel]; rw [if_pos h]

lemma choice_spec {U : Mat} {k : ℕ} (h : reductionChoice U = some k) :
    matrixHeight (reduction U k) + 1 = matrixHeight U := by
  have := List.find?_some h
  simpa using this

lemma alg_high {U : Mat} {k : ℕ} (h3 : 3 < matrixHeight U) (hc : reductionChoice U = some k) :
    algorithm1 U = algorithm1 (reduction U k) ++ [.h] ++ List.replicate k .t := by
  have hs := choice_spec hc
  unfold algorithm1
  obtain ⟨f, hf⟩ : ∃ f, matrixHeight U = f + 1 := ⟨matrixHeight U - 1, by omega⟩
  rw [hf]
  simp only [synthesisFuel]
  rw [if_neg (by omega), hc]
  simp only
  rw [show f = matrixHeight (reduction U k) by omega]

/-! ## the height step (Lemma 3) -/

lemma height_step {U : Mat} (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (hring : EntriesInRing U)
    (h3 : 3 < matrixHeight U) : (reductionChoice U).isSome = true := by
  have h0 : U false false ≠ 0 := by
    intro h; unfold matrixHeight at h3; rw [if_pos h] at h3; omega
  obtain ⟨d, hd⟩ := sde_of_ring (hring false false) h0
  have hn := height_eq hd
  have hd4 : 4 ≤ d := by omega
  have hw5 : ω ^ 5 * U true false ∈ synthesisRing := mul_mem (pow_mem om_syn _) (hring true false)
  have hu5 : Complex.normSq (U false false) + Complex.normSq (ω ^ 5 * U true false) = 1 := by
    rw [map_mul, normSq_om_pow, one_mul]; exact col_unit hU
  obtain ⟨k', hk'⟩ := denominator_changes_attainable _ _ (hring false false) hw5 hu5 d hd hd4
    (-1) (Or.inl rfl)
  have hent : reduction U (3 - k'.val) false false =
      (U false false + ω ^ 5 * U true false * ω ^ k'.val) / s2 := by
    rw [red_entry]
    have : ω ^ (7 * (3 - k'.val)) = ω ^ 5 * ω ^ k'.val := by
      rw [← pow_add]
      fin_cases k' <;> simp
      · rw [show (21:ℕ) = 5 + 8 * 2 by rfl, pow_add, pow_mul, om8]; ring
      · rw [show (14:ℕ) = 6 + 8 by rfl, pow_add, om8]; ring
      · rw [om8]
    rw [this]; ring
  rw [← hent] at hk'
  have hh := height_eq hk'
  apply List.find?_isSome.2
  refine ⟨3 - k'.val, ?_, ?_⟩
  · fin_cases k' <;> simp
  · simp only [decide_eq_true_eq]; rw [hh, hn]; omega

/-! ## main -/

lemma trace_all (B : ℕ)
    (hB : ∀ U : Mat, U ∈ Matrix.unitaryGroup Bool ℂ → EntriesInRing U → matrixHeight U ≤ 3 →
      baseDepth U ≤ B) (n : ℕ) :
    ∀ U : Mat, matrixHeight U = n → U ∈ Matrix.unitaryGroup Bool ℂ → EntriesInRing U →
      SynthesisTrace B U (algorithm1 U) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU hring
  by_cases h3 : matrixHeight U ≤ 3
  · rw [alg_low h3]
    exact SynthesisTrace.base h3 (hB U hU hring h3)
      (base_spec U ((exact_synthesis_iff U hU).1 hring)).1
  · push_neg at h3
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (height_step hU hring h3)
    rw [alg_high h3 hk]
    have hs := choice_spec hk
    exact SynthesisTrace.step h3 hk
      (ih _ (by omega) _ rfl (red_unitary hU k) (red_ring hring k))

end X4P13

open QAlgorithms.Papers.Independent.Support21.P13 in
open scoped Classical in
theorem solution :
    ∃ B : ℕ, ∀ U : Matrix Bool Bool ℂ,
      U ∈ Matrix.unitaryGroup Bool ℂ → EntriesInRing U →
      (matrixHeight U ≤ 3 → baseDepth U ≤ B ∧
        htWordMatrix (baseWord U) = U) ∧
      SynthesisTrace B U (algorithm1 U) ∧ htWordMatrix (algorithm1 U) = U := by
  obtain ⟨B, hB⟩ := (X4P13.low_finite.image baseDepth).bddAbove
  have hB' : ∀ U : Matrix Bool Bool ℂ, U ∈ Matrix.unitaryGroup Bool ℂ → EntriesInRing U →
      matrixHeight U ≤ 3 → baseDepth U ≤ B :=
    fun U hU hr hh => hB ⟨U, ⟨hU, hr, hh⟩, rfl⟩
  refine ⟨B, fun U hU hring => ⟨fun hh => ⟨hB' U hU hring hh,
    (X4P13.base_spec U ((exact_synthesis_iff U hU).1 hring)).2⟩, ?_, ?_⟩⟩
  · exact X4P13.trace_all B hB' _ U rfl hU hring
  · exact X4P13.trace_sound (X4P13.trace_all B hB' _ U rfl hU hring)
