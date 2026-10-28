-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.binaryProfileExpansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:37:12.613981+00:00
-- url     : https://prove2.me/submissions/2886f299-9679-415e-963b-35169614475b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace BPE210

open Polynomial in
lemma cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl

lemma relEnt_diag {X : Type*} [Fintype X] [DecidableEq X] (p q : X → ℝ)
    (hpq : ∀ i, q i = 0 → p i = 0) :
    relativeEntropy
      (Matrix.diagonal (fun j => (p j : ℂ))) (Matrix.diagonal (fun j => (q j : ℂ))) =
      ((∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) : ℝ) : EReal) := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
  rw [if_pos]
  · rw [cfc_diag, cfc_diag, Matrix.diagonal_mul_diagonal, Matrix.trace_sub,
      Matrix.trace_diagonal, Matrix.trace_diagonal, Complex.sub_re, Complex.re_sum, Complex.re_sum,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re]
  · intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
    rcases mul_eq_zero.mp this with h | h
    · rw [hpq i (by exact_mod_cast h)]; simp
    · rw [h, mul_zero]

open Real

/-- binary relative entropy d(r+x ‖ r) in log form -/
def Fq (x r : ℝ) : ℝ :=
  (r + x) * log (r + x) - (r + x) * log r + ((1 - r - x) * log (1 - r - x) - (1 - r - x) * log (1 - r))

lemma relEnt_bin (x r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    relativeEntropy (Matrix.diagonal ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)])
      (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)]) = ((Fq x r : ℝ) : EReal) := by
  have h1 : ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)] =
      fun j => ((![r + x, 1 - r - x] j : ℝ) : ℂ) := by
    funext j; fin_cases j <;> rfl
  have h2 : ![(r : ℂ), ((1 - r : ℝ) : ℂ)] = fun j => ((![r, 1 - r] j : ℝ) : ℂ) := by
    funext j; fin_cases j <;> rfl
  rw [h1, h2, relEnt_diag]
  · congr 1; simp [Fin.sum_univ_two, Fq]; ring
  · intro i hi; fin_cases i <;> simp at hi <;> linarith

lemma resid (z : ℝ) (hz : 0 < z) : (z - 1) ^ 2 / (2 * (1 + z)) ≤ z - 1 - log z := by
  set s := Real.sqrt z with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hz
  have hs2 : s ^ 2 = z := Real.sq_sqrt hz.le
  have hlz : log z = 2 * log s := by rw [← hs2, Real.log_pow]; norm_num
  have hl := Real.log_le_sub_one_of_pos hs0
  rw [div_le_iff₀ (by linarith)]
  have : (s - 1) ^ 2 * (2 * (1 + s ^ 2)) - (s ^ 2 - 1) ^ 2 = (s - 1) ^ 4 := by ring
  rw [← hs2] at *
  nlinarith [pow_two_nonneg ((s - 1) ^ 2), sq_nonneg (s - 1)]

lemma kl_tan (a b a0 b0 : ℝ) (ha : 0 < a) (hb : 0 < b) (ha0 : 0 < a0) (hb0 : 0 < b0) :
    a * (log a0 - log b0) + a - a0 * b / b0 +
      a * ((a0 * b / (b0 * a)) - 1) ^ 2 / (2 * (1 + a0 * b / (b0 * a)))
      ≤ a * log a - a * log b := by
  set z := a0 * b / (b0 * a) with hz
  have hz0 : 0 < z := by positivity
  have hlz : log z = log a0 + log b - log b0 - log a := by
    rw [hz, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]; ring
  have haz : a * z = a0 * b / b0 := by rw [hz]; field_simp
  have hr := resid z hz0
  have : a * ((z - 1) ^ 2 / (2 * (1 + z))) ≤ a * (z - 1 - log z) :=
    mul_le_mul_of_nonneg_left hr ha.le
  have e : a * (z - 1) ^ 2 / (2 * (1 + z)) = a * ((z - 1) ^ 2 / (2 * (1 + z))) := by ring
  have e2 : a * (z - 1 - log z) = a0 * b / b0 - a - a * (log a0 + log b - log b0 - log a) := by
    rw [← haz, hlz]; ring
  rw [e]
  linarith

lemma kl_basic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a - b ≤ a * log a - a * log b := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have h2 := mul_le_mul_of_nonneg_left h ha.le
  have e : a * (b / a - 1) = b - a := by field_simp
  rw [e] at h2
  linarith

lemma Fq_nonneg (x r : ℝ) (hr0 : 0 < r) (hr1 : r < 1 - x) (hx : 0 < x) : 0 ≤ Fq x r := by
  have h1 := kl_basic (r + x) r (by linarith) hr0
  have h2 := kl_basic (1 - r - x) (1 - r) (by linarith) (by linarith)
  unfold Fq
  linarith

/-- slope of the tangent at q0 -/
def Esl (x : ℝ) : ℝ :=
  let q0 := 1 / 2 - x / 3
  log (q0 + x) - log q0 - (log (1 - q0 - x) - log (1 - q0)) - x / q0 - x / (1 - q0)

lemma lower_main (x r : ℝ) (hx : 0 < x) (hx1 : x ≤ 1 / 4) (hr0 : 0 < r) (hr1 : r < 1 - x) :
    Fq x (1 / 2 - x / 3) - 3 * Esl x ^ 2 / (2 * x ^ 2) ≤ Fq x r := by
  set q0 := 1 / 2 - x / 3 with hq0
  have hq0p : 0 < q0 := by linarith
  have hq0x : 0 < 1 - q0 - x := by linarith
  have h1 := kl_tan (r + x) r (q0 + x) q0 (by linarith) hr0 (by linarith) hq0p
  have h2 := kl_tan (1 - r - x) (1 - r) (1 - q0 - x) (1 - q0) (by linarith) (by linarith)
    hq0x (by linarith)
  set z := (q0 + x) * r / (q0 * (r + x)) with hz
  have hz0 : 0 < z := by positivity
  have hz2 : z ≤ 2 := by
    rw [hz, div_le_iff₀ (by positivity)]; nlinarith
  have hzm : z - 1 = x * (r - q0) / (q0 * (r + x)) := by
    rw [hz]; field_simp; ring
  have hres1 : x ^ 2 * (r - q0) ^ 2 / 6 ≤ (r + x) * (z - 1) ^ 2 / (2 * (1 + z)) := by
    have hw : (r + x) * (z - 1) ^ 2 = x ^ 2 * (r - q0) ^ 2 / (q0 ^ 2 * (r + x)) := by
      rw [hzm]; field_simp
    rw [hw, div_div]
    have hD : q0 ^ 2 * (r + x) * (2 * (1 + z)) ≤ 6 := by
      have hq : q0 ^ 2 ≤ 1 / 4 := by nlinarith
      have hrx : r + x ≤ 1 := by linarith
      have : q0 ^ 2 * (r + x) ≤ 1 / 4 := by nlinarith
      nlinarith
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hD
  have hres2 : 0 ≤ (1 - r - x) * ((1 - q0 - x) * (1 - r) / ((1 - q0) * (1 - r - x)) - 1) ^ 2 /
      (2 * (1 + (1 - q0 - x) * (1 - r) / ((1 - q0) * (1 - r - x)))) := by
    apply div_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
    have : 0 ≤ (1 - q0 - x) * (1 - r) / ((1 - q0) * (1 - r - x)) := by
      apply div_nonneg <;> apply mul_nonneg <;> linarith
    linarith
  -- affine identity
  have hid : (r + x) * (log (q0 + x) - log q0) + (r + x) - (q0 + x) * r / q0 +
      ((1 - r - x) * (log (1 - q0 - x) - log (1 - q0)) + (1 - r - x) -
        (1 - q0 - x) * (1 - r) / (1 - q0)) =
      Fq x q0 + Esl x * (r - q0) := by
    unfold Fq Esl
    simp only [← hq0]
    have : 1 - q0 ≠ 0 := by linarith
    field_simp
    ring
  have hsq : 0 ≤ (x ^ 2 * (r - q0) + 3 * Esl x) ^ 2 / (6 * x ^ 2) := by positivity
  have hsq' : (x ^ 2 * (r - q0) + 3 * Esl x) ^ 2 / (6 * x ^ 2) =
      x ^ 2 * (r - q0) ^ 2 / 6 + Esl x * (r - q0) + 3 * Esl x ^ 2 / (2 * x ^ 2) := by
    field_simp; ring
  have : Fq x r = (r + x) * log (r + x) - (r + x) * log r +
      ((1 - r - x) * log (1 - r - x) - (1 - r - x) * log (1 - r)) := rfl
  linarith

lemma log_T7 (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - y ^ 6 / 6 + y ^ 7 / 7)|
      ≤ 2 * |y| ^ 8 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) (by rw [abs_neg]; linarith) 7
  rw [abs_neg, show (1:ℝ) - -y = 1 + y by ring] at h
  have e : (∑ i ∈ Finset.range 7, (-y) ^ (i + 1) / (i + 1)) + log (1 + y) =
      log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5 - y ^ 6 / 6 + y ^ 7 / 7) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  rw [e] at h
  refine h.trans ?_
  have h0 : 0 ≤ |y| := abs_nonneg y
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ |y| ^ 8 := by positivity
  norm_num
  nlinarith [mul_nonneg this (show 0 ≤ 1 - 2 * |y| by linarith)]

lemma log_T4 (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4)| ≤ 2 * |y| ^ 5 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) (by rw [abs_neg]; linarith) 4
  rw [abs_neg, show (1:ℝ) - -y = 1 + y by ring] at h
  have e : (∑ i ∈ Finset.range 4, (-y) ^ (i + 1) / (i + 1)) + log (1 + y) =
      log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
  rw [e] at h
  refine h.trans ?_
  have h0 : 0 ≤ |y| := abs_nonneg y
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ |y| ^ 5 := by positivity
  norm_num
  nlinarith [mul_nonneg this (show 0 ≤ 1 - 2 * |y| by linarith)]

lemma logs_q0 (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1 / 4) :
    log (1 / 2 - x / 3 + x) = log (1 + 4 * x / 3) - log 2 ∧
    log (1 / 2 - x / 3) = log (1 + -(2 * x / 3)) - log 2 ∧
    log (1 - (1 / 2 - x / 3) - x) = log (1 + -(4 * x / 3)) - log 2 ∧
    log (1 - (1 / 2 - x / 3)) = log (1 + 2 * x / 3) - log 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 1 / 2 - x / 3 + x = (1 + 4 * x / 3) / 2 by ring, Real.log_div (by linarith) (by norm_num)]
  · rw [show 1 / 2 - x / 3 = (1 + -(2 * x / 3)) / 2 by ring, Real.log_div (by linarith) (by norm_num)]
  · rw [show 1 - (1 / 2 - x / 3) - x = (1 + -(4 * x / 3)) / 2 by ring,
      Real.log_div (by linarith) (by norm_num)]
  · rw [show 1 - (1 / 2 - x / 3) = (1 + 2 * x / 3) / 2 by ring, Real.log_div (by linarith) (by norm_num)]

lemma Fq0_bound (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1 / 4) :
    |Fq x (1 / 2 - x / 3) - (2 * x ^ 2 + 4 / 9 * x ^ 4 + 32 / 135 * x ^ 6)| ≤ 50 * x ^ 8 := by
  obtain ⟨e1, e2, e3, e4⟩ := logs_q0 x hx hx1
  have hF : Fq x (1 / 2 - x / 3) =
      (1 / 2 + 2 * x / 3) * (log (1 + 4 * x / 3) - log (1 + -(2 * x / 3))) +
      (1 / 2 - 2 * x / 3) * (log (1 + -(4 * x / 3)) - log (1 + 2 * x / 3)) := by
    unfold Fq; rw [e1, e2, e3, e4]; ring
  have a1 : |4 * x / 3| = 4 * x / 3 := abs_of_pos (by positivity)
  have a2 : |-(2 * x / 3)| = 2 * x / 3 := by rw [abs_neg]; exact abs_of_pos (by positivity)
  have a3 : |-(4 * x / 3)| = 4 * x / 3 := by rw [abs_neg]; exact abs_of_pos (by positivity)
  have a4 : |2 * x / 3| = 2 * x / 3 := abs_of_pos (by positivity)
  have t1 := log_T7 (4 * x / 3) (by rw [a1]; linarith)
  have t2 := log_T7 (-(2 * x / 3)) (by rw [a2]; linarith)
  have t3 := log_T7 (-(4 * x / 3)) (by rw [a3]; linarith)
  have t4 := log_T7 (2 * x / 3) (by rw [a4]; linarith)
  rw [a1] at t1; rw [a2] at t2; rw [a3] at t3; rw [a4] at t4
  rw [abs_le] at t1 t2 t3 t4
  have hp : 0 ≤ 1 / 2 + 2 * x / 3 := by linarith
  have hm : 0 ≤ 1 / 2 - 2 * x / 3 := by linarith
  have hx8 : 0 ≤ x ^ 8 := by positivity
  rw [hF, abs_le]
  constructor
  · linarith [mul_le_mul_of_nonneg_left t1.1 hp, mul_le_mul_of_nonneg_left t2.2 hp,
      mul_le_mul_of_nonneg_left t3.1 hm, mul_le_mul_of_nonneg_left t4.2 hm]
  · linarith [mul_le_mul_of_nonneg_left t1.2 hp, mul_le_mul_of_nonneg_left t2.1 hp,
      mul_le_mul_of_nonneg_left t3.2 hm, mul_le_mul_of_nonneg_left t4.1 hm]

lemma Esl_bound (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1 / 4) : |Esl x| ≤ 40 * x ^ 5 := by
  obtain ⟨e1, e2, e3, e4⟩ := logs_q0 x hx hx1
  have hE : Esl x = log (1 + 4 * x / 3) - log (1 + -(2 * x / 3)) -
      (log (1 + -(4 * x / 3)) - log (1 + 2 * x / 3)) -
      (4 * x + 16 * x ^ 3 / 9 + 64 * x ^ 5 / (9 * (9 - 4 * x ^ 2))) := by
    have hd : x / (1 / 2 - x / 3) + x / (1 - (1 / 2 - x / 3)) =
        4 * x + 16 * x ^ 3 / 9 + 64 * x ^ 5 / (9 * (9 - 4 * x ^ 2)) := by
      have h1 : (1 / 2 - x / 3) ≠ 0 := by linarith
      have h2 : (1 - (1 / 2 - x / 3)) ≠ 0 := by linarith
      have h3 : (9 - 4 * x ^ 2) ≠ 0 := by nlinarith
      have ha : x / (1 / 2 - x / 3) + x / (1 - (1 / 2 - x / 3)) = 36 * x / (9 - 4 * x ^ 2) := by
        rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]; ring
      have hb : 64 * x ^ 5 / (9 * (9 - 4 * x ^ 2)) = 36 * x / (9 - 4 * x ^ 2) - 4 * x - 16 * x ^ 3 / 9 := by
        have hw : (9 - 4 * x ^ 2) * (9 - 4 * x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ h3
        simp only [div_eq_mul_inv, mul_inv]
        linear_combination (-(4 * x + 16 * x ^ 3 / 9)) * hw
      rw [ha, hb]; ring
    unfold Esl; simp only []
    rw [e1, e2, e3, e4, ← hd]; ring
  have hr0 : 0 ≤ 64 * x ^ 5 / (9 * (9 - 4 * x ^ 2)) := by
    apply div_nonneg (by positivity); nlinarith
  have hr1 : 64 * x ^ 5 / (9 * (9 - 4 * x ^ 2)) ≤ x ^ 5 := by
    rw [div_le_iff₀ (by nlinarith)]
    have : 0 ≤ x ^ 5 := by positivity
    nlinarith [mul_nonneg this (show 0 ≤ 17 - 36 * x ^ 2 by nlinarith)]
  have a1 : |4 * x / 3| = 4 * x / 3 := abs_of_pos (by positivity)
  have a2 : |-(2 * x / 3)| = 2 * x / 3 := by rw [abs_neg]; exact abs_of_pos (by positivity)
  have a3 : |-(4 * x / 3)| = 4 * x / 3 := by rw [abs_neg]; exact abs_of_pos (by positivity)
  have a4 : |2 * x / 3| = 2 * x / 3 := abs_of_pos (by positivity)
  have t1 := log_T4 (4 * x / 3) (by rw [a1]; linarith)
  have t2 := log_T4 (-(2 * x / 3)) (by rw [a2]; linarith)
  have t3 := log_T4 (-(4 * x / 3)) (by rw [a3]; linarith)
  have t4 := log_T4 (2 * x / 3) (by rw [a4]; linarith)
  rw [a1] at t1; rw [a2] at t2; rw [a3] at t3; rw [a4] at t4
  rw [abs_le] at t1 t2 t3 t4
  have hx5 : 0 ≤ x ^ 5 := by positivity
  rw [hE, abs_le]
  constructor <;> linarith

end BPE210

open QAlgorithms.Papers.Independent.Gap48.P40 BPE210 in
theorem solution :
    (∀ x : ℝ, 0 < x → x < 1 → binaryProfile x ≠ ⊤ ∧ binaryProfile x ≠ ⊥) ∧
    (fun x : ℝ => (binaryProfile x).toReal -
      (2 * x ^ 2 + (4 / 9 : ℝ) * x ^ 4 + (32 / 135 : ℝ) * x ^ 6))
      =O[nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)] (fun x : ℝ => x ^ 8) := by
  have hlow : ∀ x : ℝ, 0 < x → x < 1 → ((0 : ℝ) : EReal) ≤ binaryProfile x := by
    intro x hx _
    apply le_sInf
    rintro v ⟨r, hr0, hr1, rfl⟩
    rw [relEnt_bin x r hr0 (by linarith)]
    exact EReal.coe_le_coe_iff.mpr (Fq_nonneg x r hr0 hr1 hx)
  have hup : ∀ x r : ℝ, 0 < x → 0 < r → r < 1 - x → binaryProfile x ≤ ((Fq x r : ℝ) : EReal) := by
    intro x r hx hr0 hr1
    apply sInf_le
    exact ⟨r, hr0, hr1, (relEnt_bin x r hr0 (by linarith)).symm⟩
  have hfin : ∀ x : ℝ, 0 < x → x < 1 → binaryProfile x ≠ ⊤ ∧ binaryProfile x ≠ ⊥ := by
    intro x hx hx1
    exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) (hup x ((1 - x) / 2) hx (by linarith) (by linarith)),
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (hlow x hx hx1)⟩
  refine ⟨hfin, ?_⟩
  apply Asymptotics.IsBigO.of_bound (50 + 2400)
  have hmem : Set.Ioo (0:ℝ) (1 / 4) ∈ nhdsWithin 0 (Set.Ioo (0:ℝ) 1) :=
    mem_nhdsWithin.mpr ⟨Set.Iio (1 / 4), isOpen_Iio, by norm_num, fun y hy => ⟨hy.2.1, hy.1⟩⟩
  filter_upwards [hmem] with x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hx1' : x ≤ 1 / 4 := hx1.le
  obtain ⟨hT, hB⟩ := hfin x hx0 (by linarith)
  have hb : binaryProfile x = ((binaryProfile x).toReal : EReal) := (EReal.coe_toReal hT hB).symm
  set b := (binaryProfile x).toReal
  have hU : b ≤ Fq x (1 / 2 - x / 3) := by
    have := hup x (1 / 2 - x / 3) hx0 (by linarith) (by linarith)
    rw [hb] at this; exact EReal.coe_le_coe_iff.mp this
  have hL : Fq x (1 / 2 - x / 3) - 3 * Esl x ^ 2 / (2 * x ^ 2) ≤ b := by
    have : ((Fq x (1 / 2 - x / 3) - 3 * Esl x ^ 2 / (2 * x ^ 2) : ℝ) : EReal) ≤ binaryProfile x := by
      apply le_sInf
      rintro v ⟨r, hr0, hr1, rfl⟩
      rw [relEnt_bin x r hr0 (by linarith)]
      exact EReal.coe_le_coe_iff.mpr (lower_main x r hx0 hx1' hr0 hr1)
    rw [hb] at this; exact EReal.coe_le_coe_iff.mp this
  have h1 := abs_le.mp (Fq0_bound x hx0 hx1')
  have h2 := Esl_bound x hx0 hx1'
  have hE2 : Esl x ^ 2 ≤ (40 * x ^ 5) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hE3 : 3 * Esl x ^ 2 / (2 * x ^ 2) ≤ 2400 * x ^ 8 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hx8 : 0 ≤ x ^ 8 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx8, abs_le]
  constructor <;> nlinarith
