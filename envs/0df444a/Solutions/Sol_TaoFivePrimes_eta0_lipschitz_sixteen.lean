-- Prove2me | solution 1 for TaoFivePrimes.eta0_lipschitz_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:14:31.781038+00:00
-- url     : https://prove2.me/submissions/e25799a0-e9bc-48b6-b078-c37b255af6c7

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes

namespace TaoS14

theorem log_lip {a b : ℝ} (ha : 1/4 ≤ a) (hb : 1/4 ≤ b) :
    |Real.log a - Real.log b| ≤ 4 * |a - b| := by
  have key : ∀ u v : ℝ, 1/4 ≤ u → 1/4 ≤ v → v ≤ u →
      Real.log u - Real.log v ≤ 4 * (u - v) := by
    intro u v hu hv huv
    have hv0 : (0:ℝ) < v := by linarith
    have hu0 : (0:ℝ) < u := by linarith
    have h1 : Real.log u - Real.log v = Real.log (u / v) :=
      (Real.log_div (ne_of_gt hu0) (ne_of_gt hv0)).symm
    have h2 : Real.log (u / v) ≤ u / v - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : u / v - 1 = (u - v) / v := by field_simp
    have h4 : (u - v) / v ≤ 4 * (u - v) := by
      rw [div_le_iff₀ hv0]
      nlinarith
    linarith [h1 ▸ h2, h3 ▸ h2]
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith [Real.log_le_log (by linarith : (0:ℝ) < b) h]),
      abs_of_nonneg (by linarith)]
    exact key a b ha hb h
  · rw [abs_of_nonpos (by linarith [Real.log_le_log (by linarith : (0:ℝ) < a) h]),
      abs_of_nonpos (by linarith)]
    have := key b a hb ha h
    linarith

theorem eta0_eq_min {t : ℝ} (h1 : 1/4 ≤ t) (h2 : t ≤ 1) :
    eta0 t = min (4 * (2 * Real.log 2 + Real.log t)) (-4 * Real.log t) := by
  have ht : (0:ℝ) < t := by linarith
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt ht)
  have hlow : (0:ℝ) ≤ 2 * Real.log 2 + Real.log t := by
    have h : Real.log (1/4 : ℝ) ≤ Real.log t := Real.log_le_log (by norm_num) h1
    have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    linarith [h4 ▸ h]
  have hhigh : Real.log t ≤ 0 := by
    rw [show (0:ℝ) = Real.log 1 by simp]
    exact Real.log_le_log ht h2
  unfold eta0
  rw [if_pos ht, hlog]
  rcases abs_cases (Real.log 2 + Real.log t) with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he, max_eq_right (by linarith), min_eq_right (by linarith)]; ring
  · rw [he, max_eq_right (by linarith), min_eq_left (by linarith)]; ring

theorem eta0_lip_core {s t : ℝ} (hs1 : 1/4 ≤ s) (hs2 : s ≤ 1)
    (ht1 : 1/4 ≤ t) (ht2 : t ≤ 1) : |eta0 s - eta0 t| ≤ 16 * |s - t| := by
  rw [eta0_eq_min hs1 hs2, eta0_eq_min ht1 ht2]
  have hA : |4 * (2 * Real.log 2 + Real.log s) - 4 * (2 * Real.log 2 + Real.log t)|
      ≤ 16 * |s - t| := by
    have : 4 * (2 * Real.log 2 + Real.log s) - 4 * (2 * Real.log 2 + Real.log t)
        = 4 * (Real.log s - Real.log t) := by ring
    rw [this, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    linarith [log_lip hs1 ht1]
  have hB : |(-4) * Real.log s - (-4) * Real.log t| ≤ 16 * |s - t| := by
    have : (-4) * Real.log s - (-4) * Real.log t = (-4) * (Real.log s - Real.log t) := by ring
    rw [this, abs_mul, abs_of_nonpos (by norm_num : (-4:ℝ) ≤ 0)]
    linarith [log_lip hs1 ht1]
  rcases abs_sub_le_iff.mp hA with ⟨hA1, hA2⟩
  rcases abs_sub_le_iff.mp hB with ⟨hB1, hB2⟩
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;>
    · rcases min_cases (4 * (2 * Real.log 2 + Real.log s)) (-4 * Real.log s) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases min_cases (4 * (2 * Real.log 2 + Real.log t)) (-4 * Real.log t) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      rw [e1, e2] <;>
      simp only [neg_mul] at * <;> linarith [min_le_left (4 * (2 * Real.log 2 + Real.log s)) (-(4 * Real.log s)),
        min_le_right (4 * (2 * Real.log 2 + Real.log s)) (-(4 * Real.log s)),
        min_le_left (4 * (2 * Real.log 2 + Real.log t)) (-(4 * Real.log t)),
        min_le_right (4 * (2 * Real.log 2 + Real.log t)) (-(4 * Real.log t))]


theorem eta0_eq_zero_of_le' {t : ℝ} (h : t ≤ 1/4) : eta0 t = 0 := by
  unfold eta0
  by_cases ht : 0 < t
  · rw [if_pos ht, max_eq_left, mul_zero]
    have h2 : Real.log (2*t) ≤ Real.log (1/2) := Real.log_le_log (by linarith) (by linarith)
    have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
      rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [h3] at h2
    linarith [neg_le_abs (Real.log (2*t))]
  · rw [if_neg ht]

theorem eta0_eq_zero_of_ge' {t : ℝ} (h : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  have ht : 0 < t := by linarith
  rw [if_pos ht, max_eq_left, mul_zero]
  have h2 : Real.log 2 ≤ Real.log (2*t) := Real.log_le_log (by norm_num) (by linarith)
  linarith [le_abs_self (Real.log (2*t))]

/-- The clamp onto the support `[1/4, 1]` of `η₀`. -/
noncomputable def cl (t : ℝ) : ℝ := max (1/4) (min 1 t)

theorem cl_lower (t : ℝ) : 1/4 ≤ cl t := le_max_left _ _

theorem cl_upper (t : ℝ) : cl t ≤ 1 := max_le (by norm_num) (min_le_left _ _)

theorem cl_lipschitz : LipschitzWith 1 cl :=
  (LipschitzWith.id.const_min (1:ℝ)).const_max (1/4)

theorem cl_dist (s t : ℝ) : |cl s - cl t| ≤ |s - t| := by
  have := cl_lipschitz.dist_le_mul s t
  simpa [Real.dist_eq] using this

theorem eta0_cl (t : ℝ) : eta0 (cl t) = eta0 t := by
  unfold cl
  rcases le_total t (1/4) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    rw [eta0_eq_zero_of_le' h, eta0_eq_min (le_refl _) (by norm_num)]
    have h4 : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1/4 : ℝ) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.log_pow, Real.log_inv]
      push_cast; ring
    rw [h4]
    have : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [min_eq_left (by linarith)]
    ring
  · rcases le_total t 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (by norm_num)]
      rw [eta0_eq_zero_of_ge' h', eta0_eq_min (by norm_num) (le_refl _)]
      simp
      exact Real.log_nonneg (by norm_num)

/-- **Tao, equation (s1-4).**  `‖η₀'‖_{L^∞(ℝ)} = 16`, in the form that `η₀` is
`16`-Lipschitz. -/
theorem eta0_lipschitz : LipschitzWith 16 eta0 := by
  refine LipschitzWith.of_dist_le_mul (fun s t => ?_)
  rw [Real.dist_eq, Real.dist_eq, ← eta0_cl s, ← eta0_cl t]
  refine le_trans (eta0_lip_core (cl_lower s) (cl_upper s) (cl_lower t) (cl_upper t)) ?_
  have := cl_dist s t
  push_cast
  linarith

end TaoS14

theorem solution : LipschitzWith 16 TaoFivePrimes.eta0 := TaoS14.eta0_lipschitz
