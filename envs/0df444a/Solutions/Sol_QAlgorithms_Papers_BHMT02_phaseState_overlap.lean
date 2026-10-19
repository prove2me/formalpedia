-- Prove2me | solution 1 for QAlgorithms.Papers.BHMT02.phaseState_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:52:29.172565+00:00
-- url     : https://prove2.me/submissions/58327b6e-9adf-41f3-bb7f-d30419d8dbf9

import Definitions.Def_QAlgorithms_Defs_PhaseOracles
set_option autoImplicit false
open scoped Real ComplexConjugate
open QAlgorithms

private lemma bo_inner (M : ℕ) (ω0 ω1 : ℝ) :
    inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1) =
      (∑ y : Fin M, Complex.exp (2 * π * Complex.I * ((ω1 - ω0 : ℝ) : ℂ) * (y : ℕ))) / M := by
  have hs : (Real.sqrt M : ℂ) ^ 2 = M := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg M)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold bhmtPhaseState dotProduct
  simp only [Pi.star_apply, Complex.star_def, map_div₀, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  rw [div_mul_div_comm, ← pow_two, hs, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma bo_exp_norm (t : ℝ) :
    Complex.normSq (Complex.exp (2 * π * Complex.I * (t : ℂ)) - 1) =
      4 * Real.sin (π * t) ^ 2 := by
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hc := Real.cos_two_mul (π * t)
  have ht := Real.sin_sq_add_cos_sq (2 * π * t)
  rw [show 2 * π * t = 2 * (π * t) by ring] at ht ⊢
  nlinarith [Real.sin_sq_add_cos_sq (π * t)]

private lemma bo_sin_abs (x : ℝ) : Real.sin |x| ^ 2 = Real.sin x ^ 2 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, Real.sin_neg, neg_sq]

private lemma bo_sin_dist (x y : ℝ) (k : ℕ) :
    Real.sin ((k : ℝ) * circDist x y * π) ^ 2 =
      Real.sin (π * ((k : ℝ) * (y - x))) ^ 2 := by
  have ha : (k : ℝ) * circDist x y * π =
      |(k : ℝ) * ((x - y) - (round (x - y) : ℝ)) * π| := by
    simp [circDist, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k), abs_of_pos Real.pi_pos]
  rw [ha, bo_sin_abs, Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have he : 2 * ((k : ℝ) * (x - y - (round (x - y) : ℝ)) * π) =
      2 * ((k : ℝ) * (x - y) * π) - ((k : ℤ) * round (x - y) : ℤ) * (2 * π) := by
    push_cast
    ring
  rw [he, Real.cos_sub_int_mul_two_pi]
  congr 2
  rw [show 2 * ((k : ℝ) * (x - y) * π) = -(2 * (π * ((k : ℝ) * (y - x)))) by ring,
    Real.cos_neg]

theorem solution (M : ℕ) (hM : 0 < M) (ω0 ω1 : ℝ) (h0 : 0 ≤ ω0) (h0' : ω0 < 1)
    (h1 : 0 ≤ ω1) (h1' : ω1 < 1) :
    (circDist ω0 ω1 = 0 →
      ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 = 1) ∧
    (circDist ω0 ω1 ≠ 0 →
      ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 =
        Real.sin ((M : ℝ) * circDist ω0 ω1 * Real.pi) ^ 2 /
          ((M : ℝ) ^ 2 * Real.sin (circDist ω0 ω1 * Real.pi) ^ 2)) := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  constructor
  · intro hd
    have he : ω0 - ω1 = (round (ω0 - ω1) : ℝ) := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hd)
    have hzi : (-1 : ℤ) < round (ω0 - ω1) ∧ round (ω0 - ω1) < 1 := by
      constructor
      · exact_mod_cast (show (-1 : ℝ) < (round (ω0 - ω1) : ℝ) by linarith)
      · exact_mod_cast (show (round (ω0 - ω1) : ℝ) < 1 by linarith)
    have hz : round (ω0 - ω1) = 0 := by omega
    have heq : ω0 = ω1 := by simp only [hz, Int.cast_zero] at he; linarith
    rw [bo_inner, heq]
    simp [hM.ne']
  · intro hd
    let d : ℝ := ω1 - ω0
    let r : ℂ := Complex.exp (2 * π * Complex.I * (d : ℂ))
    let s : ℂ := ∑ y ∈ Finset.range M, r ^ y
    have ha : inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1) = s / M := by
      rw [bo_inner]
      congr 1
      calc
        _ = ∑ y : Fin M, r ^ (y : ℕ) := by
          apply Finset.sum_congr rfl
          intro y hy
          dsimp [r, d]
          rw [← Complex.exp_nat_mul]
          congr 1
          ring
        _ = s := Fin.sum_univ_eq_sum_range (fun y : ℕ => r ^ y) M
    have hg : s * (r - 1) = r ^ M - 1 := geom_sum_mul r M
    have hr : r ^ M = Complex.exp (2 * π * Complex.I * ((M * d : ℝ) : ℂ)) := by
      dsimp [r]
      rw [← Complex.exp_nat_mul]
      push_cast
      congr 1
      ring
    have hn := congrArg Complex.normSq hg
    rw [Complex.normSq_mul, hr, bo_exp_norm (M * d), bo_exp_norm d] at hn
    have hsd := bo_sin_dist ω0 ω1 1
    simp only [Nat.cast_one, one_mul] at hsd
    have hsm := bo_sin_dist ω0 ω1 M
    have hp : 0 < circDist ω0 ω1 := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
    have hb : circDist ω0 ω1 ≤ 1 / 2 := abs_sub_round _
    have hsin : Real.sin (circDist ω0 ω1 * π) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
    have hns : ‖inner ℂ (bhmtPhaseState M ω0) (bhmtPhaseState M ω1)‖ ^ 2 =
        Complex.normSq s / (M : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ha, map_div₀, Complex.normSq_natCast, pow_two]
    rw [hns, hsm, hsd]
    dsimp [d] at hn
    have hs2 : Real.sin (π * (ω1 - ω0)) ^ 2 ≠ 0 := by
      rw [← hsd]
      exact pow_ne_zero 2 hsin
    apply (div_eq_div_iff (pow_ne_zero 2 hm) (mul_ne_zero (pow_ne_zero 2 hm) hs2)).mpr
    nlinarith only [congrArg (fun v : ℝ => v * (M : ℝ)^2) hn]

#print axioms solution
