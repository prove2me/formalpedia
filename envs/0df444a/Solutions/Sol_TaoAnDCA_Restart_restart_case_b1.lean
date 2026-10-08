-- Prove2me | solution 1 for TaoAnDCA.Restart.restart_case_b1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:54:34.947764+00:00
-- url     : https://prove2.me/submissions/7833b6ab-f67b-4b3f-8f2f-32f7019259f6

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

open TaoAnDCA.Restart

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar)
    (w : EuclideanSpace ℝ (Fin n)) (hw : inner ℝ w (A w + lamStar • w) < 0)
    (hcase : ‖xs‖ < r ∨ (‖xs‖ = r ∧ inner ℝ w xs ≠ 0)) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    restartGamma w xs r s ≠ 0 ∧
      ‖w‖ ^ 2 * restartGamma w xs r s ^ 2 + 2 * inner ℝ w xs * restartGamma w xs r s
        + ‖xs‖ ^ 2 - r ^ 2 = 0 ∧
      ‖xs + restartGamma w xs r s • w‖ = r ∧
      TaoAnDCA.TRS.quad A b (xs + restartGamma w xs r s • w) =
        TaoAnDCA.TRS.quad A b xs + restartGamma w xs r s ^ 2 / 2 * inner ℝ w (A w + lamStar • w) ∧
      TaoAnDCA.TRS.quad A b (xs + restartGamma w xs r s • w) < TaoAnDCA.TRS.quad A b xs := by
  have hwn : w ≠ 0 := by intro hz; simp [hz] at hw
  have ha : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwn)
  have han : ‖w‖ ^ 2 ≠ 0 := ne_of_gt ha
  let a := ‖w‖ ^ 2
  let c := inner ℝ w xs
  let d := ‖xs‖ ^ 2 - r ^ 2
  let g := restartGamma w xs r s
  have hg : g ≠ 0 ∧ a * g ^ 2 + 2 * c * g + d = 0 := by
    rcases hcase with hi | ⟨he, hc⟩
    · have hne : ‖xs‖ ≠ r := ne_of_lt hi
      have hd : d < 0 := by dsimp [d]; nlinarith [norm_nonneg xs]
      have hrad : 0 ≤ c ^ 2 - a * d := by
        have : a * d < 0 := mul_neg_of_pos_of_neg ha hd
        nlinarith [sq_nonneg c]
      have hsqrt := Real.sq_sqrt hrad
      have hgs : a * g = -c + s * Real.sqrt (c ^ 2 - a * d) := by
        dsimp [g, restartGamma]
        rw [if_neg hne]
        dsimp [a, c, d]
        field_simp
      have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
      have heq : a * g ^ 2 + 2 * c * g + d = 0 := by
        have hsq : (a * g + c) ^ 2 = c ^ 2 - a * d := by
          calc
            _ = (s * Real.sqrt (c ^ 2 - a * d)) ^ 2 := by rw [hgs]; ring
            _ = c ^ 2 - a * d := by rw [mul_pow, hs2, one_mul, hsqrt]
        have hx : a * (a * g ^ 2 + 2 * c * g + d) = 0 := by
          nlinarith [hsq]
        exact (mul_eq_zero.mp hx).resolve_left han
      refine ⟨?_, heq⟩
      intro hz
      rw [hz] at heq
      nlinarith
    · have hgs : a * g = -2 * c := by
        dsimp [g, restartGamma]
        rw [if_pos he]
        dsimp [a, c]
        field_simp
      have hd : d = 0 := by simp [d, he]
      refine ⟨?_, ?_⟩
      · intro hz
        rw [hz] at hgs
        apply hc
        change c = 0
        linarith
      · rw [hd]
        nlinarith [congrArg (fun z : ℝ => g * z) hgs]
  have hn2 : ‖xs + g • w‖ ^ 2 = r ^ 2 := by
    have he : ‖xs + g • w‖ ^ 2 = ‖xs‖ ^ 2 + 2 * g * inner ℝ w xs + g ^ 2 * ‖w‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [real_inner_comm xs w]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    dsimp [a, c, d] at hg
    nlinarith [hg.2]
  have hn : ‖xs + g • w‖ = r := by nlinarith [norm_nonneg (xs + g • w)]
  have hf : TaoAnDCA.TRS.quad A b (xs + g • w) =
      TaoAnDCA.TRS.quad A b xs + g ^ 2 / 2 * inner ℝ w (A w + lamStar • w) := by
    have hk := hkkt.2.1
    have h1 := congrArg (fun z => inner ℝ w z) hk
    simp only [inner_add_right, inner_neg_right, real_inner_smul_right] at h1
    have hc : inner ℝ xs (A w) = inner ℝ w (A xs) := by
      calc
        _ = inner ℝ (A w) xs := real_inner_comm _ _
        _ = inner ℝ w (A xs) := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) w xs
    have hlam : lamStar * (‖xs‖ ^ 2 - r ^ 2) = 0 := by
      nlinarith [congrArg (fun z : ℝ => (‖xs‖ + r) * z) hkkt.2.2.1]
    have heq := hg.2
    dsimp [a, c, d] at heq
    have hm := congrArg (fun z : ℝ => lamStar * z) heq
    simp only [TaoAnDCA.TRS.quad, map_add, map_smul, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [hc]
    simp only [real_inner_comm xs w, real_inner_comm b w] at *
    nlinarith [congrArg (fun z : ℝ => g * z) h1]
  refine ⟨hg.1, ?_, hn, hf, ?_⟩
  · dsimp [a, c, d] at hg
    linarith [hg.2]
  · rw [hf]
    have hp : 0 < g ^ 2 / 2 := div_pos (sq_pos_of_ne_zero hg.1) (by norm_num)
    have := mul_neg_of_pos_of_neg hp hw
    linarith

#print axioms solution
