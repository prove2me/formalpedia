-- Prove2me | solution 1 for QubitFreqSensing.fact_5_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:58:58.863069+00:00
-- url     : https://prove2.me/submissions/a05eaae0-130b-4796-bf6a-d6e608090ff0

import Mathlib
import Definitions.Def_QubitFreqSensing_Mobius
namespace QubitFreqSensing
private theorem mob_sign_norm {ε : ℝ} (he : ε = 1 ∨ ε = -1) : ‖(ε : ℂ)‖ = 1 := by
  rcases he with rfl | rfl <;> simp

private theorem mob_den_ne {ε : ℝ} {a z : ℂ} (he : ε = 1 ∨ ε = -1) (ha : ‖a‖ < 1)
    (hz : ‖z‖ ≤ 1) : 1 + (ε : ℂ) * (starRingEnd ℂ) a * z ≠ 0 := by
  have hs : ‖(ε : ℂ) * (starRingEnd ℂ) a * z‖ < 1 := by
    simpa only [norm_mul, mob_sign_norm he,one_mul,Complex.norm_conj] using (mul_le_of_le_one_right (norm_nonneg a) hz).trans_lt ha
  intro h
  have heq : (ε : ℂ) * (starRingEnd ℂ) a * z = -1 := by linear_combination h
  simp [heq] at hs

private theorem mob_defect {ε : ℝ} {a z : ℂ} (he : ε = 1 ∨ ε = -1)
    (hd : 1 + (ε : ℂ) * (starRingEnd ℂ) a * z ≠ 0) :
    1 - ‖mob ε a z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 + (ε : ℂ) * (starRingEnd ℂ) a * z‖ ^ 2 := by
  rw [mob, norm_div, div_pow]
  rw [one_sub_div (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)), div_left_inj' (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd))]
  rcases he with rfl | rfl <;>
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

end QubitFreqSensing

open QubitFreqSensing

theorem solution (a : ℂ) (ha : ‖a‖ < 1) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    (DifferentiableOn ℂ (mob ε a) (Metric.ball 0 1) ∧
      Set.MapsTo (mob ε a) (Metric.ball 0 1) (Metric.ball 0 1) ∧ mob ε a 0 = a) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖mob ε a z‖ ≤ 1 ∧ (‖mob ε a z‖ = 1 ↔ ‖z‖ = 1)) ∧
    (∀ z : ℂ, 1 + (ε : ℂ) * (starRingEnd ℂ) a * z ≠ 0 →
      1 - ‖mob ε a z‖ ^ 2 =
        (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 + (ε : ℂ) * (starRingEnd ℂ) a * z‖ ^ 2) ∧
    (∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun n : ℕ => ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * (ε : ℂ) ^ (n + 1) *
          (-(starRingEnd ℂ) a) ^ n * z ^ (n + 1))
        (mob ε a z - a)) := by
  have posA : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have inside {z : ℂ} (hz : ‖z‖ < 1) : ‖mob ε a z‖ < 1 := by
    have hd := mob_den_ne hε ha hz.le
    have posZ : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hh := (mob_defect hε hd).symm ▸ div_pos (mul_pos posA posZ) (sq_pos_of_pos (norm_pos_iff.mpr hd))
    nlinarith [norm_nonneg (mob ε a z)]
  refine ⟨⟨?_,?_,by simp [mob]⟩,?_,fun _ hd => mob_defect hε hd,?_⟩
  · intro z hz
    have hn := mob_den_ne hε ha (le_of_lt (by simpa using hz : ‖z‖ < 1))
    unfold mob
    exact DifferentiableWithinAt.div (c := fun w : ℂ => a + (ε : ℂ) * w)
      (d := fun w : ℂ => 1 + (ε : ℂ) * (starRingEnd ℂ) a * w) (by fun_prop) (by fun_prop) hn
  · intro z hz
    simpa using inside (by simpa using hz : ‖z‖ < 1)
  · intro z hz
    rcases lt_or_eq_of_le hz with hlt | hunit
    · exact ⟨(inside hlt).le, ⟨fun hh => False.elim ((inside hlt).ne hh),fun hh => False.elim (hlt.ne hh)⟩⟩
    · have heq := mob_defect hε (mob_den_ne hε ha hz)
      rw [hunit] at heq
      simp only [one_pow,sub_self,mul_zero,zero_div] at heq
      have hh : ‖mob ε a z‖ = 1 := by nlinarith [norm_nonneg (mob ε a z)]
      simp [hh,hunit]
  · intro z hz
    let r := (ε : ℂ) * (-(starRingEnd ℂ) a) * z
    have hr : ‖r‖ < 1 := by
      simpa only [r,norm_mul,mob_sign_norm hε,one_mul,norm_neg,Complex.norm_conj] using (mul_le_of_le_one_right (norm_nonneg a) hz.le).trans_lt ha
    let k := ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * (ε : ℂ) * z
    have hk := (hasSum_geometric_of_norm_lt_one hr).mul_left k
    have term (n : ℕ) : k * r ^ n = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * (ε : ℂ) ^ (n+1) *
        (-(starRingEnd ℂ) a) ^ n * z ^ (n+1) := by simp only [k,r,mul_pow,pow_succ]; ring
    have den : 1 - r = 1 + (ε : ℂ) * (starRingEnd ℂ) a * z := by dsimp [r]; ring
    have hd := mob_den_ne hε ha hz.le
    have total : k * (1 - r)⁻¹ = mob ε a z - a := by
      rw [den,mob,← div_eq_mul_inv]
      field_simp [hd]
      dsimp [k]
      push_cast
      rw [← Complex.mul_conj' a]
      ring
    rw [← total]
    simpa only [term] using hk
