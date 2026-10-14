-- Prove2me | solution 1 for ThreeSum1960614.quartic_switch_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:29:20.483199+00:00
-- url     : https://prove2.me/submissions/4472d78e-20c0-4a4b-b951-fac4ce81e6f5

-- Derivative comparison follows the pinned upstream Parameters.lean method.
-- The rational quartic, logarithmic coefficient certificate and expansion are new.
import Theorems.Thm_ThreeSum1960614_quartic_geometry
import Theorems.Thm_ThreeSum1960614_log_coefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open ThreeSum1960614 Set

private theorem log_one_add_lower_four {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let F : ℝ → ℝ := fun y => Real.log (1 + y) - y + y ^ 2 / 2 - y ^ 3 / 3 + y ^ 4 / 4
  have hd : ∀ y ∈ Ici (0 : ℝ), HasDerivAt F (y ^ 4 / (1 + y)) y := by
    intro y hy
    have hn : 1 + y ≠ 0 := by have hy0 : 0 ≤ y := hy; linarith
    have h := (((((hasDerivAt_id y).const_add 1).log hn).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
        (((hasDerivAt_id y).pow 3).div_const 3)
    have h' := h.add (((hasDerivAt_id y).pow 4).div_const 4)
    change HasDerivAt F _ y at h'
    apply h'.congr_deriv
    dsimp only [id_eq]
    field_simp [hn]
    <;> ring
  have hm : MonotoneOn F (Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hy0 : 0 ≤ y := interior_subset hy
    positivity
  have h := hm (by simp : (0 : ℝ) ∈ Ici (0 : ℝ)) hx hx
  have hz : F 0 = 0 := by norm_num [F]
  rw [hz] at h
  dsimp [F] at h
  linarith

private theorem neg_log_one_sub_lower_four {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / 4 ≤ -Real.log (1 - t) := by
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h := sum_le_hasSum (Finset.range 4)
    (fun n _ => div_nonneg (pow_nonneg ht0 _) (by positivity)) hs
  norm_num [Finset.sum_range_succ] at h
  exact h

private theorem entropy_eq (t : ℝ) :
    entropy t = (-t * Real.log t - (1 - t) * Real.log (1 - t)) / Real.log 2 := by
  simp only [entropy, Real.binEntropy, Real.log_inv]
  ring

private noncomputable def gammaNumerator (t : ℝ) : ℝ :=
  (1 - t) * Real.log (1 - t) + (231 + t) * Real.log (231 + t) - 231 * Real.log 231

private theorem gamma_formula {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    gamma 232 t = gammaNumerator t / Real.log 2 := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h231 : (231 + t : ℝ) ≠ 0 := by linarith [ht.1]
  unfold gamma
  rw [entropy_eq, entropy_eq]
  norm_num only [Nat.cast_ofNat]
  rw [show 1 - (1 - t) / 232 = (231 + t) / 232 by ring]
  norm_num
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (232 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (231 : ℝ) ≠ 0) (by norm_num : (232 : ℝ) ≠ 0),
    Real.log_div h1 (by norm_num : (232 : ℝ) ≠ 0),
    Real.log_div h231 (by norm_num : (232 : ℝ) ≠ 0)]
  simp only [Real.log_one]
  unfold gammaNumerator
  ring

private theorem hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by
  have hd := (((((hasDerivAt_id t).const_mul 785174904).add
    (((hasDerivAt_id t).pow 2).const_mul 72447023)).add
      (((hasDerivAt_id t).pow 3).const_mul 24044466)).add
        (((hasDerivAt_id t).pow 4).const_mul 12022459)).div_const 100000000
  change HasDerivAt phi _ t at hd
  apply hd.congr_deriv
  dsimp [phiDeriv]
  ring

private theorem hasDerivAt_gammaNumerator {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    HasDerivAt gammaNumerator (Real.log (231 + t) - Real.log (1 - t)) t := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h231 : (231 + t : ℝ) ≠ 0 := by linarith [ht.1]
  have hd1 := (hasDerivAt_id t).const_sub 1
  have hd231 := (hasDerivAt_id t).const_add 231
  have hd := ((hd1.mul (hd1.log h1)).add (hd231.mul (hd231.log h231))).sub_const
    (231 * Real.log 231)
  change HasDerivAt gammaNumerator _ t at hd
  apply hd.congr_deriv
  dsimp only [id_eq]
  field_simp [h1, h231]
  <;> ring

private theorem gamma_derivative_above_phi {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    Real.log 2 * phiDeriv t ≤ Real.log (231 + t) - Real.log (1 - t) := by
  have ht0 : 0 ≤ t := ht.1
  obtain ⟨_, _, hlinear, hquadratic, hcubic, hquartic⟩ :=
    ThreeSum1960614.log_coefficients
  have hq := mul_le_mul_of_nonneg_right hquadratic ht0
  have hc := mul_le_mul_of_nonneg_right hcubic (sq_nonneg t)
  have h4 := mul_le_mul_of_nonneg_right hquartic (pow_nonneg ht0 3)
  have hadd := log_one_add_lower_four (x := t / 231) (by positivity)
  have hneg := neg_log_one_sub_lower_four ht0 (by linarith [ht.2])
  have hlog : Real.log (231 + t) = Real.log 231 + Real.log (1 + t / 231) := by
    rw [show 231 + t = 231 * (1 + t / 231) by ring,
      Real.log_mul (by norm_num : (231 : ℝ) ≠ 0) (by positivity : (1 + t / 231 : ℝ) ≠ 0)]
  have hrem : 0 ≤ (1 - (1 / 231 : ℝ) ^ 4) * t ^ 4 / 4 := by
    apply div_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht0 4)) (by norm_num)
  dsimp [phiDeriv]
  nlinarith

private theorem phi_le_gamma {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma 232 t := by
  let F : ℝ → ℝ := fun y => gammaNumerator y - Real.log 2 * phi y
  let F' : ℝ → ℝ := fun y =>
    Real.log (231 + y) - Real.log (1 - y) - Real.log 2 * phiDeriv y
  have hd : ∀ y ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt F (F' y) y := by
    intro y hy
    exact (hasDerivAt_gammaNumerator hy).sub ((hasDerivAt_phi y).const_mul (Real.log 2))
  have hm : MonotoneOn F (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / 2))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    exact sub_nonneg.mpr (gamma_derivative_above_phi (interior_subset hy))
  have h := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2)) ht ht.1
  have hz : F 0 = 0 := by norm_num [F, gammaNumerator, phi]
  rw [hz] at h
  rw [gamma_formula ht, le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  dsimp [F] at h
  nlinarith

theorem solution (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma 232 t ∧ 0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by
  obtain ⟨hp, hb, htan⟩ := ThreeSum1960614.quartic_geometry t ht
  exact ⟨phi_le_gamma ht, hp, hb, htan⟩
