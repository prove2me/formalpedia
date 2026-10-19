-- Prove2me | solution 1 for Wigner.fock_wigner
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:30:36.122987+00:00
-- url     : https://prove2.me/submissions/102b1502-208e-4b6a-9743-6bd61ddc2ba2

import Mathlib
import Definitions.Def_wigner
import Definitions.Def_wigner_states


open MeasureTheory

namespace FWAux
open Wigner

lemma H_rec (n : ℕ) (z : ℝ) :
    hermiteP (n + 1) z = 2 * z * hermiteP n z - 2 * n * hermiteP (n - 1) z := by
  rcases n with _ | n
  · simp [hermiteP]
  · simp only [hermiteP, Nat.add_sub_cancel]; push_cast; ring

lemma H_deriv : ∀ (n : ℕ) (z : ℝ), HasDerivAt (hermiteP n) (2 * n * hermiteP (n - 1) z) z
  | 0, z => by simpa [hermiteP] using hasDerivAt_const z (1:ℝ)
  | 1, z => by
      have : hermiteP 1 = fun z => 2 * z := by funext z; simp [hermiteP]
      rw [this]; simpa [hermiteP] using (hasDerivAt_id z).const_mul 2
  | n + 2, z => by
      have hf : hermiteP (n + 2) = fun z => 2 * z * hermiteP (n + 1) z - 2 * (n + 1) * hermiteP n z := by
        funext z; simp [hermiteP]
      rw [hf]
      have h1 := H_deriv (n + 1) z
      have h0 := H_deriv n z
      have := (((hasDerivAt_id' z).const_mul 2).mul h1).sub (h0.const_mul (2 * ((n:ℝ) + 1)))
      have this' : HasDerivAt (fun w => 2 * w * hermiteP (n + 1) w - 2 * ((n:ℝ) + 1) * hermiteP n w) _ z :=
        this
      refine this'.congr_deriv ?_
      have hr := H_rec n z
      simp only [Nat.add_sub_cancel, show n + 2 - 1 = n + 1 by omega]
      push_cast
      linear_combination (-(2 * ((n:ℝ) + 1))) * hr

lemma H_bound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |hermiteP n z| ≤ C * (1 + |z|) ^ n
  | 0 => ⟨1, zero_le_one, fun z => by simp [hermiteP]⟩
  | 1 => ⟨2, by norm_num, fun z => by
      simp only [hermiteP, pow_one, abs_mul, abs_two]; nlinarith [abs_nonneg z]⟩
  | n + 2 => by
      obtain ⟨C1, hC1, h1⟩ := H_bound (n + 1)
      obtain ⟨C0, hC0, h0⟩ := H_bound n
      refine ⟨2 * C1 + 2 * (n + 1) * C0, by positivity, fun z => ?_⟩
      simp only [hermiteP]
      have hz : 1 ≤ 1 + |z| := by linarith [abs_nonneg z]
      have hp1 : (1 + |z|) ^ n ≤ (1 + |z|) ^ (n + 2) := pow_le_pow_right₀ hz (by omega)
      have hp2 : |z| * (1 + |z|) ^ (n + 1) ≤ (1 + |z|) ^ (n + 2) := by
        rw [pow_succ _ (n + 1)]; nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + |z|) (n + 1), abs_nonneg z]
      calc |2 * z * hermiteP (n + 1) z - 2 * (↑n + 1) * hermiteP n z|
          ≤ 2 * |z| * |hermiteP (n + 1) z| + 2 * (n + 1) * |hermiteP n z| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos (by positivity : (0:ℝ) < 2 * (n + 1))]
        _ ≤ 2 * |z| * (C1 * (1 + |z|) ^ (n + 1)) + 2 * (n + 1) * (C0 * (1 + |z|) ^ n) := by
            gcongr
            · exact h1 z
            · exact h0 z
        _ ≤ (2 * C1 + 2 * (n + 1) * C0) * (1 + |z|) ^ (n + 2) := by
            nlinarith [mul_le_mul_of_nonneg_left hp2 hC1, mul_le_mul_of_nonneg_left hp1
              (by positivity : (0:ℝ) ≤ 2 * (n + 1) * C0)]

end FWAux


open MeasureTheory Complex

namespace FWAux
open Wigner

/-- polynomially bounded continuous functions -/
def PB (q : ℝ → ℝ) : Prop := Continuous q ∧ ∃ C : ℝ, ∃ N : ℕ, ∀ y, |q y| ≤ C * (1 + |y|) ^ N

lemma PB.mul {q r : ℝ → ℝ} (hq : PB q) (hr : PB r) : PB (fun y => q y * r y) := by
  obtain ⟨hqc, C, N, hC⟩ := hq
  obtain ⟨hrc, D, M, hD⟩ := hr
  refine ⟨hqc.mul hrc, C * D, N + M, fun y => ?_⟩
  rw [abs_mul, pow_add]
  have h0 : 0 ≤ C * (1 + |y|) ^ N := (abs_nonneg _).trans (hC y)
  calc |q y| * |r y| ≤ (C * (1 + |y|) ^ N) * (D * (1 + |y|) ^ M) :=
        mul_le_mul (hC y) (hD y) (abs_nonneg _) h0
    _ = C * D * ((1 + |y|) ^ N * (1 + |y|) ^ M) := by ring

lemma PB.add {q r : ℝ → ℝ} (hq : PB q) (hr : PB r) : PB (fun y => q y + r y) := by
  obtain ⟨hqc, C, N, hC⟩ := hq
  obtain ⟨hrc, D, M, hD⟩ := hr
  refine ⟨hqc.add hrc, |C| + |D|, N + M, fun y => ?_⟩
  have hy : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have h1 : (1 + |y|) ^ N ≤ (1 + |y|) ^ (N + M) := pow_le_pow_right₀ hy (by omega)
  have h2 : (1 + |y|) ^ M ≤ (1 + |y|) ^ (N + M) := pow_le_pow_right₀ hy (by omega)
  have hp : 0 ≤ (1 + |y|) ^ N := by positivity
  have hp2 : 0 ≤ (1 + |y|) ^ M := by positivity
  calc |q y + r y| ≤ |q y| + |r y| := abs_add_le _ _
    _ ≤ C * (1 + |y|) ^ N + D * (1 + |y|) ^ M := add_le_add (hC y) (hD y)
    _ ≤ |C| * (1 + |y|) ^ (N + M) + |D| * (1 + |y|) ^ (N + M) :=
        add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C) hp).trans
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)))
          ((mul_le_mul_of_nonneg_right (le_abs_self D) hp2).trans
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg D)))
    _ = (|C| + |D|) * (1 + |y|) ^ (N + M) := by ring

lemma PB.const (c : ℝ) : PB (fun _ => c) := ⟨continuous_const, |c|, 0, fun y => by simp⟩

lemma PB.id : PB (fun y => y) := ⟨continuous_id, 1, 1, fun y => by simp⟩

lemma PB.smul {q : ℝ → ℝ} (c : ℝ) (hq : PB q) : PB (fun y => c * q y) := (PB.const c).mul hq

lemma PB.sub {q r : ℝ → ℝ} (hq : PB q) (hr : PB r) : PB (fun y => q y - r y) := by
  have := hq.add (hr.smul (-1)); simpa [sub_eq_add_neg] using this

lemma H_cont (n : ℕ) : Continuous (hermiteP n) := by
  rw [continuous_iff_continuousAt]; intro z
  exact (H_deriv n z).continuousAt

lemma PB.H_shift (n : ℕ) (x s : ℝ) (hs : |s| = 1) : PB (fun y => hermiteP n (x + s * y)) := by
  obtain ⟨C, hC0, hC⟩ := H_bound n
  refine ⟨(H_cont n).comp (by fun_prop), C * (1 + |x|) ^ n, n, fun y => ?_⟩
  refine (hC _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC0
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have : |x + s * y| ≤ |x| + |y| := by
    refine (abs_add_le _ _).trans ?_; rw [abs_mul, hs, one_mul]
  nlinarith [abs_nonneg x, abs_nonneg y]

lemma gauss_bound (N : ℕ) (y : ℝ) :
    (1 + |y|) ^ N * Real.exp (-y ^ 2) ≤ N.factorial * Real.exp (3 / 2) * Real.exp (-(1/2) * y ^ 2) := by
  have h1 := Real.pow_div_factorial_le_exp (1 + |y|) (by positivity) N
  have hf : (0:ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf] at h1
  have h2 : Real.exp (1 + |y|) * Real.exp (-y ^ 2) ≤ Real.exp (3 / 2) * Real.exp (-(1/2) * y ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : |y| ≤ 1 / 2 + y ^ 2 / 2 := by nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
    linarith
  calc (1 + |y|) ^ N * Real.exp (-y ^ 2) ≤ Real.exp (1 + |y|) * N.factorial * Real.exp (-y ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = N.factorial * (Real.exp (1 + |y|) * Real.exp (-y ^ 2)) := by ring
    _ ≤ N.factorial * (Real.exp (3 / 2) * Real.exp (-(1/2) * y ^ 2)) := by gcongr
    _ = _ := by ring

variable (x p : ℝ)

/-- the weight `e^{-x²-y²} e^{2ipy}` -/
noncomputable def wt (y : ℝ) : ℂ := (Real.exp (-x ^ 2 - y ^ 2) : ℂ) * Complex.exp ((2 * p * y : ℝ) * I)

lemma norm_wt (y : ℝ) : ‖wt x p y‖ = Real.exp (-x ^ 2 - y ^ 2) := by
  rw [wt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma int_PB {q : ℝ → ℝ} (hq : PB q) : Integrable (fun y => (q y : ℂ) * wt x p y) := by
  obtain ⟨hqc, C, N, hC⟩ := hq
  have hg := (integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul
    (|C| * N.factorial * Real.exp (3 / 2) * Real.exp (-x ^ 2))
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · apply Continuous.aestronglyMeasurable
    unfold wt; fun_prop
  · rw [norm_mul, norm_wt, Complex.norm_real, Real.norm_eq_abs]
    have hb := gauss_bound N y
    have e1 : Real.exp (-x ^ 2 - y ^ 2) = Real.exp (-x ^ 2) * Real.exp (-y ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1]
    have hC' : |q y| ≤ |C| * (1 + |y|) ^ N := (hC y).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    calc |q y| * (Real.exp (-x ^ 2) * Real.exp (-y ^ 2))
        ≤ |C| * (1 + |y|) ^ N * (Real.exp (-x ^ 2) * Real.exp (-y ^ 2)) :=
          mul_le_mul_of_nonneg_right hC' (by positivity)
      _ = |C| * Real.exp (-x ^ 2) * ((1 + |y|) ^ N * Real.exp (-y ^ 2)) := by ring
      _ ≤ |C| * Real.exp (-x ^ 2) * (N.factorial * Real.exp (3 / 2) * Real.exp (-(1/2) * y ^ 2)) := by
          gcongr
      _ = _ := by ring

end FWAux


open MeasureTheory Complex

namespace FWAux
open Wigner

variable (x p : ℝ)

lemma PB_Hp (n : ℕ) : PB (fun y => hermiteP n (x + y)) := by
  simpa using PB.H_shift n x 1 (by simp)

lemma PB_Hm (k : ℕ) : PB (fun y => hermiteP k (x - y)) := by
  have := PB.H_shift k x (-1) (by simp)
  simpa [sub_eq_add_neg] using this

lemma PB_HH (n k : ℕ) : PB (fun y => hermiteP n (x + y) * hermiteP k (x - y)) :=
  (PB_Hp x n).mul (PB_Hm x k)

noncomputable def FA (n k : ℕ) (y : ℝ) : ℂ :=
  ((hermiteP n (x + y) * hermiteP k (x - y) : ℝ) : ℂ) * wt x p y

noncomputable def FY (n k : ℕ) (y : ℝ) : ℂ :=
  ((2 * y * (hermiteP n (x + y) * hermiteP k (x - y)) : ℝ) : ℂ) * wt x p y

noncomputable def II (n k : ℕ) : ℂ := ∫ y, FA x p n k y

lemma FA_int (n k : ℕ) : Integrable (FA x p n k) := int_PB x p (PB_HH x n k)

lemma FY_int (n k : ℕ) : Integrable (FY x p n k) := int_PB x p ((PB.id.smul 2).mul (PB_HH x n k))

lemma wt_deriv (y : ℝ) : HasDerivAt (wt x p) (wt x p y * (((-2 * y : ℝ) : ℂ) + 2 * p * I)) y := by
  have hr : HasDerivAt (fun y : ℝ => Real.exp (-x ^ 2 - y ^ 2)) (Real.exp (-x ^ 2 - y ^ 2) * (-2 * y)) y := by
    have := ((hasDerivAt_pow 2 y).const_sub (-x ^ 2)).exp
    exact this.congr_deriv (by push_cast; ring)
  have h1 := hr.ofReal_comp
  have hl : HasDerivAt (fun y : ℝ => 2 * p * y) (2 * p) y := by
    simpa using (hasDerivAt_id y).const_mul (2 * p)
  have h2 := (hl.ofReal_comp.mul_const I).cexp
  have h3 := h1.mul h2
  unfold wt
  refine h3.congr_deriv ?_
  push_cast; ring

lemma K2_eq (n k : ℕ) :
    ∫ y, FY x p n k y =
      2 * n * II x p (n - 1) k - 2 * k * II x p n (k - 1) + 2 * p * I * II x p n k := by
  have hderiv : ∀ y, HasDerivAt (FA x p n k) ((2 * n : ℂ) * FA x p (n - 1) k y - (2 * k : ℂ) * FA x p n (k - 1) y
      + 2 * p * I * FA x p n k y - FY x p n k y) y := by
    intro y
    have h1' : HasDerivAt (fun y => hermiteP n (x + y)) (2 * n * hermiteP (n - 1) (x + y)) y :=
      (H_deriv n (x + y)).comp_const_add x y
    have h2' : HasDerivAt (fun y => hermiteP k (x - y)) (-(2 * k * hermiteP (k - 1) (x - y))) y :=
      (H_deriv k (x - y)).comp_const_sub x y
    have h3 := ((h1'.mul h2').ofReal_comp).mul (wt_deriv x p y)
    unfold FA
    refine h3.congr_deriv ?_
    unfold FY
    simp only [Pi.mul_apply]
    push_cast; ring
  have iA := (FA_int x p (n - 1) k).const_mul (2 * n : ℂ)
  have iB := (FA_int x p n (k - 1)).const_mul (2 * k : ℂ)
  have iC := (FA_int x p n k).const_mul (2 * p * I)
  have iAB : Integrable (fun y => (2 * n : ℂ) * FA x p (n - 1) k y - (2 * k : ℂ) * FA x p n (k - 1) y) :=
    iA.sub iB
  have iABC : Integrable (fun y => (2 * n : ℂ) * FA x p (n - 1) k y - (2 * k : ℂ) * FA x p n (k - 1) y
      + 2 * p * I * FA x p n k y) := iAB.add iC
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (iABC.sub (FY_int x p n k)) (FA_int x p n k)
  rw [integral_sub iABC (FY_int x p n k), integral_add iAB iC, integral_sub iA iB,
    integral_const_mul, integral_const_mul, integral_const_mul] at h0
  unfold II
  linear_combination -h0

lemma II_rec (n k : ℕ) : II x p (n + 1) k = 2 * (x + p * I) * II x p n k - 2 * k * II x p n (k - 1) := by
  have hK := K2_eq x p n k
  have e : FA x p (n + 1) k = fun y => (2 * x : ℂ) * FA x p n k y + FY x p n k y -
      (2 * n : ℂ) * FA x p (n - 1) k y := by
    funext y; unfold FA FY; rw [H_rec]; push_cast; ring
  have i1 := (FA_int x p n k).const_mul (2 * x : ℂ)
  have i3 := (FA_int x p (n - 1) k).const_mul (2 * n : ℂ)
  have i12 : Integrable (fun y => (2 * x : ℂ) * FA x p n k y + FY x p n k y) := i1.add (FY_int x p n k)
  unfold II
  rw [e, integral_sub i12 i3, integral_add i1 (FY_int x p n k), integral_const_mul, integral_const_mul]
  rw [hK]; unfold II; ring

lemma II_base (k : ℕ) : II x p 0 (k + 1) = 2 * (x - p * I) * II x p 0 k := by
  have hK := K2_eq x p 0 k
  have e : FA x p 0 (k + 1) = fun y => (2 * x : ℂ) * FA x p 0 k y - FY x p 0 k y -
      (2 * k : ℂ) * FA x p 0 (k - 1) y := by
    funext y; unfold FA FY; rw [H_rec]; simp only [hermiteP]; push_cast; ring
  have i1 := (FA_int x p 0 k).const_mul (2 * x : ℂ)
  have i3 := (FA_int x p 0 (k - 1)).const_mul (2 * k : ℂ)
  have i12 : Integrable (fun y => (2 * x : ℂ) * FA x p 0 k y - FY x p 0 k y) := i1.sub (FY_int x p 0 k)
  unfold II
  rw [e, integral_sub i12 i3, integral_sub i1 (FY_int x p 0 k), integral_const_mul, integral_const_mul]
  rw [hK]; unfold II; simp; ring

lemma II_zero : II x p 0 0 = (Real.sqrt Real.pi * Real.exp (-(x ^ 2 + p ^ 2)) : ℝ) := by
  unfold II FA wt
  have e : ∀ y : ℝ, ((hermiteP 0 (x + y) * hermiteP 0 (x - y) : ℝ) : ℂ) *
      ((Real.exp (-x ^ 2 - y ^ 2) : ℂ) * Complex.exp ((2 * p * y : ℝ) * I)) =
      Complex.exp ((-1 : ℂ) * (y : ℂ) ^ 2 + (2 * p * I) * y + (-(x : ℂ) ^ 2)) := by
    intro y
    simp only [hermiteP, mul_one, one_mul, Complex.ofReal_one]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [e]
  rw [integral_cexp_quadratic (by simp)]
  have hpi : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
    push_cast; ring_nf
  rw [hpi]
  push_cast
  congr 1
  congr 1
  ring_nf
  rw [Complex.I_sq]; ring

end FWAux


open MeasureTheory Complex Finset

namespace FWAux
open Wigner

noncomputable def tt (a b : ℂ) (n k j : ℕ) : ℂ :=
  (n.choose j : ℂ) * (k.descFactorial j : ℂ) * (-2) ^ j * a ^ (n - j) * b ^ (k - j)

noncomputable def SS (a b : ℂ) (n k : ℕ) : ℂ := ∑ j ∈ range (n + 1), tt a b n k j

lemma descF_succ (k i : ℕ) : ((k.descFactorial (i + 1) : ℕ) : ℂ) = k * ((k - 1).descFactorial i : ℕ) := by
  rcases k with _ | k
  · simp [Nat.zero_descFactorial_succ]
  · rw [Nat.succ_descFactorial_succ]; push_cast; simp

lemma SS_succ (a b : ℂ) (n k : ℕ) : SS a b (n + 1) k = a * SS a b n k - 2 * k * SS a b n (k - 1) := by
  unfold SS
  rw [sum_range_succ']
  have hsplit : ∀ i ∈ range (n + 1), tt a b (n + 1) k (i + 1) =
      (-2 * k) * tt a b n (k - 1) i +
        (n.choose (i + 1) : ℂ) * (k.descFactorial (i + 1) : ℂ) * (-2) ^ (i + 1) * a ^ (n - i) *
          b ^ (k - (i + 1)) := by
    intro i hi
    unfold tt
    rw [Nat.choose_succ_succ', descF_succ]
    have e1 : n + 1 - (i + 1) = n - i := by omega
    have e2 : k - (i + 1) = k - 1 - i := by omega
    rw [e1, e2]
    push_cast
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum]
  -- the remaining terms give a * SS n k
  have hB : ∑ i ∈ range (n + 1), (n.choose (i + 1) : ℂ) * (k.descFactorial (i + 1) : ℂ) *
        (-2) ^ (i + 1) * a ^ (n - i) * b ^ (k - (i + 1)) + tt a b (n + 1) k 0 =
      a * ∑ j ∈ range (n + 1), tt a b n k j := by
    rw [mul_sum, sum_range_succ' (fun j => a * tt a b n k j), sum_range_succ]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    have : ∀ i ∈ range n, (n.choose (i + 1) : ℂ) * (k.descFactorial (i + 1) : ℂ) *
        (-2) ^ (i + 1) * a ^ (n - i) * b ^ (k - (i + 1)) = a * tt a b n k (i + 1) := by
      intro i hi
      have hi' : i < n := mem_range.mp hi
      unfold tt
      have e1 : n - i = (n - (i + 1)) + 1 := by omega
      rw [e1, pow_succ]; ring
    rw [sum_congr rfl this]
    unfold tt; simp; ring
  linear_combination hB

lemma II_closed (x p : ℝ) : ∀ n k : ℕ,
    II x p n k = II x p 0 0 * SS (2 * (x + p * I)) (2 * (x - p * I)) n k := by
  intro n
  induction n with
  | zero =>
    intro k
    induction k with
    | zero => simp [SS, tt]
    | succ k ih =>
      rw [II_base, ih]
      simp only [SS, tt, zero_add, sum_range_one, Nat.choose_self, Nat.descFactorial_zero, pow_zero,
        Nat.sub_zero, Nat.cast_one, one_mul, mul_one]
      ring
  | succ n ih =>
    intro k
    rw [II_rec, ih, ih, SS_succ]
    ring

end FWAux


open Finset

namespace FWAux
open Wigner

noncomputable def EL (m : ℕ) (z : ℝ) : ℝ := ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (-z) ^ i / i.factorial

lemma choose_id (m j : ℕ) :
    ((m + 2 : ℕ) : ℝ) * ((m + 2).choose (j + 1) : ℝ) + ((m + 1 : ℕ) : ℝ) * (m.choose (j + 1) : ℝ) =
      (2 * m + 3 : ℝ) * ((m + 1).choose (j + 1) : ℝ) + ((j + 1 : ℕ) : ℝ) * ((m + 1).choose j : ℝ) := by
  have F1 : (m + 2).choose (j + 1) = (m + 1).choose j + (m + 1).choose (j + 1) := Nat.choose_succ_succ' _ _
  have F3 : (m + 1).choose (j + 1) = m.choose j + m.choose (j + 1) := Nat.choose_succ_succ' _ _
  have F4 := Nat.choose_mul_succ_eq m j
  rw [F1]
  push_cast
  rcases le_or_gt j (m + 1) with hj | hj
  · have F4' : (m.choose j : ℝ) * (m + 1) = ((m + 1).choose j : ℝ) * ((m + 1 : ℝ) - j) := by
      have := congrArg (fun t : ℕ => (t : ℝ)) F4
      push_cast [Nat.cast_sub hj] at this
      linarith
    rw [F3]; push_cast
    linear_combination -F4'
  · have h0 : (m + 1).choose j = 0 := Nat.choose_eq_zero_of_lt hj
    have h1 : (m + 1).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : m.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, h1, h2]; simp

/-- extend the sum range with zero terms -/
lemma EL_ext (m t : ℕ) (z : ℝ) :
    EL m z = ∑ i ∈ range (m + 1 + t), (m.choose i : ℝ) * (-z) ^ i / i.factorial := by
  unfold EL
  conv_rhs => rw [sum_range_add]
  have : ∑ i ∈ range t, (m.choose (m + 1 + i) : ℝ) * (-z) ^ (m + 1 + i) / (m + 1 + i).factorial = 0 := by
    apply sum_eq_zero; intro i _
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [this, add_zero]

lemma EL_rec (m : ℕ) (z : ℝ) :
    ((m : ℝ) + 2) * EL (m + 2) z = (2 * (m + 1) + 1 - z) * EL (m + 1) z - (m + 1) * EL m z := by
  rw [EL_ext (m + 2) 0, EL_ext (m + 1) 1, EL_ext m 2]
  simp only [add_zero, show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega,
    show m + 2 + 1 = m + 3 by omega]
  -- z * E(m+1) as a shifted sum
  have hz : z * ∑ i ∈ range (m + 3), ((m + 1).choose i : ℝ) * (-z) ^ i / i.factorial =
      -∑ i ∈ range (m + 3), (((i + 1 : ℕ) : ℝ) * ((m + 1).choose i : ℝ)) * (-z) ^ (i + 1) /
        (i + 1).factorial := by
    rw [mul_sum, ← sum_neg_distrib]
    apply sum_congr rfl; intro i _
    rw [Nat.factorial_succ]; push_cast
    have : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    field_simp; ring
  rw [sub_mul, hz, mul_sum, mul_sum, mul_sum]
  rw [sum_range_succ' (fun i => ((m : ℝ) + 2) * (((m + 2).choose i : ℝ) * (-z) ^ i / i.factorial)),
    sum_range_succ' (fun i => (2 * ((m:ℝ) + 1) + 1) * (((m + 1).choose i : ℝ) * (-z) ^ i / i.factorial)),
    sum_range_succ' (fun i => ((m:ℝ) + 1) * ((m.choose i : ℝ) * (-z) ^ i / i.factorial))]
  rw [sum_range_succ (fun i => (((i + 1 : ℕ) : ℝ) * ((m + 1).choose i : ℝ)) * (-z) ^ (i + 1) /
        (i + 1).factorial)]
  have hlast : (((m + 2 + 1 : ℕ) : ℝ) * ((m + 1).choose (m + 2) : ℝ)) * (-z) ^ (m + 2 + 1) /
      (m + 2 + 1).factorial = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hlast, add_zero]
  have hterm : ∀ i ∈ range (m + 2),
      ((m : ℝ) + 2) * (((m + 2).choose (i + 1) : ℝ) * (-z) ^ (i + 1) / (i + 1).factorial) =
      (2 * ((m:ℝ) + 1) + 1) * (((m + 1).choose (i + 1) : ℝ) * (-z) ^ (i + 1) / (i + 1).factorial) +
        (((i + 1 : ℕ) : ℝ) * ((m + 1).choose i : ℝ)) * (-z) ^ (i + 1) / (i + 1).factorial -
        ((m:ℝ) + 1) * ((m.choose (i + 1) : ℝ) * (-z) ^ (i + 1) / (i + 1).factorial) := by
    intro i _
    have := choose_id m i
    push_cast at this
    have hf : ((i + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (i + 1).factorial_ne_zero
    push_cast
    field_simp
    linear_combination ((-z) ^ (i + 1)) * this
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_add_distrib]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.factorial_zero, div_one, mul_one]
  ring

lemma laguerre_eq : ∀ (m : ℕ) (z : ℝ), laguerreL m z = EL m z
  | 0, z => by simp [laguerreL, EL]
  | 1, z => by
      simp [laguerreL, EL, sum_range_succ]; ring
  | m + 2, z => by
      rw [laguerreL, laguerre_eq (m + 1) z, laguerre_eq m z]
      have h := EL_rec m z
      have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      linear_combination -h

end FWAux


open MeasureTheory Complex Finset

namespace FWAux
open Wigner

lemma integrand_eq (m : ℕ) (x p y : ℝ) :
    wignerIntegrand (fockState m) 1 x p y =
      (((Real.pi ^ (-(1 / 2 : ℝ))) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) : ℝ) : ℂ) * FA x p m m y := by
  unfold wignerIntegrand fockState FA wt
  rw [Complex.conj_ofReal]
  have hpos : (0:ℝ) < (2 : ℝ) ^ m * (m.factorial : ℝ) := by positivity
  have hs := Real.sq_sqrt hpos.le
  have hsp := Real.sqrt_pos.mpr hpos
  have hpi : Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(1 / 4 : ℝ)) = Real.pi ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add Real.pi_pos]; norm_num
  have hexp : Real.exp (-(x + y) ^ 2 / 2) * Real.exp (-(x - y) ^ 2 / 2) = Real.exp (-x ^ 2 - y ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : ((2 * p * y / 1 : ℝ) : ℂ) = ((2 * p * y : ℝ) : ℂ) := by simp
  rw [e2]
  have key : (Real.pi ^ (-(1 / 4 : ℝ)) * hermiteP m (x + y) * Real.exp (-(x + y) ^ 2 / 2) /
        √((2:ℝ) ^ m * (m.factorial : ℝ))) *
      (Real.pi ^ (-(1 / 4 : ℝ)) * hermiteP m (x - y) * Real.exp (-(x - y) ^ 2 / 2) /
        √((2:ℝ) ^ m * (m.factorial : ℝ))) =
      Real.pi ^ (-(1 / 2 : ℝ)) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
        (hermiteP m (x + y) * hermiteP m (x - y) * Real.exp (-x ^ 2 - y ^ 2)) := by
    rw [← hpi, ← hexp]
    field_simp
    rw [hs]; ring
  have := congrArg (fun t : ℝ => (t : ℂ)) key
  push_cast at this ⊢
  linear_combination (Complex.exp (2 * p * y * I)) * this

lemma wigner_eq (m : ℕ) (x p : ℝ) :
    wigner (fockState m) 1 x p =
      Real.exp (-(x ^ 2 + p ^ 2)) / ((2 : ℝ) ^ m * (m.factorial : ℝ) * Real.pi) *
        ∑ j ∈ range (m + 1), (m.choose j : ℝ) * (m.descFactorial j : ℝ) * (-2) ^ j *
          (4 * (x ^ 2 + p ^ 2)) ^ (m - j) := by
  unfold wigner wignerIntegral
  simp_rw [integrand_eq]
  rw [integral_const_mul]
  have hII : ∫ y, FA x p m m y = II x p m m := rfl
  rw [hII, II_closed, II_zero]
  have hSS : SS (2 * (x + p * I)) (2 * (x - p * I)) m m =
      ((∑ j ∈ range (m + 1), (m.choose j : ℝ) * (m.descFactorial j : ℝ) * (-2) ^ j *
          (4 * (x ^ 2 + p ^ 2)) ^ (m - j) : ℝ) : ℂ) := by
    unfold SS tt
    push_cast
    apply sum_congr rfl; intro j _
    rw [mul_assoc _ ((2 * (↑x + ↑p * I)) ^ (m - j)), ← mul_pow]
    congr 2
    ring_nf; rw [Complex.I_sq]; ring
  rw [hSS]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpi : Real.pi ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]; norm_num
  have hpos : (0:ℝ) < (2 : ℝ) ^ m * (m.factorial : ℝ) := by positivity
  field_simp
  rw [hpi, one_mul]

lemma sum_eq_EL (m : ℕ) (r2 : ℝ) :
    (∑ j ∈ range (m + 1), (m.choose j : ℝ) * (m.descFactorial j : ℝ) * (-2) ^ j * (4 * r2) ^ (m - j)) =
      (2 : ℝ) ^ m * m.factorial * ((-1) ^ m * EL m (2 * r2)) := by
  rw [← sum_range_reflect]
  unfold EL
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have e1 : m + 1 - 1 - i = m - i := by omega
  rw [e1, Nat.choose_symm hi', show m - (m - i) = i by omega]
  have hd : (m.descFactorial (m - i) : ℝ) * (i.factorial : ℝ) = m.factorial := by
    have := Nat.factorial_mul_descFactorial (show m - i ≤ m by omega)
    rw [show m - (m - i) = i by omega] at this
    exact_mod_cast (by rw [mul_comm]; exact this)
  have hf : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hm : (-2 : ℝ) ^ (m - i) * 2 ^ i = (-1) ^ (m - i) * 2 ^ m := by
    rw [neg_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hi']
  have hsign : ((-1 : ℝ) ^ (m - i)) = (-1) ^ m * (-1) ^ i := by
    have : (-1 : ℝ) ^ m = (-1) ^ (m - i) * (-1) ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
    rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  have key : (-2 : ℝ) ^ (m - i) * 4 ^ i = 2 ^ m * (-1) ^ m * (-2) ^ i := by
    have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
    rw [h4, ← mul_assoc, hm, hsign, neg_pow (2:ℝ) i]; ring
  rw [← hd]
  have e3 : (-(2 * r2)) ^ i = (-2 : ℝ) ^ i * r2 ^ i := by rw [show -(2 * r2) = (-2) * r2 by ring, mul_pow]
  rw [e3]
  field_simp
  rw [mul_pow]
  linear_combination ((m.choose i : ℝ) * r2 ^ i) * key

end FWAux

open FWAux in
theorem fock_wigner_main (m : ℕ) (x p : ℝ) :
    Wigner.wigner (Wigner.fockState m) 1 x p =
      (-1 : ℝ) ^ m / Real.pi * Real.exp (-(x ^ 2 + p ^ 2)) *
        Wigner.laguerreL m (2 * (x ^ 2 + p ^ 2)) := by
  rw [wigner_eq, sum_eq_EL, laguerre_eq]
  have hpos : (0:ℝ) < (2 : ℝ) ^ m * (m.factorial : ℝ) := by positivity
  field_simp

open MeasureTheory in
theorem solution (m : ℕ) (x p : ℝ) :
    Wigner.wigner (Wigner.fockState m) 1 x p =
      (-1 : ℝ) ^ m / Real.pi * Real.exp (-(x ^ 2 + p ^ 2)) *
        Wigner.laguerreL m (2 * (x ^ 2 + p ^ 2)) :=
  fock_wigner_main m x p
