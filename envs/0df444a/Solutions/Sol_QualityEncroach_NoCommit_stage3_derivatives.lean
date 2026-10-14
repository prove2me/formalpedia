-- Prove2me | solution 1 for QualityEncroach.NoCommit.stage3_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:05:54.026306+00:00
-- url     : https://prove2.me/submissions/f78fb18d-d0bb-4483-9c6d-740e37b213b2

import Definitions.Def_QualityEncroach_NoCommit_Game
open QualityEncroach.NoCommit

private lemma ratio_deriv (a b c d e t : ℝ) (hd : d ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (fun s => (a+b*s+c*s^2)^2/(d*s)+e)
      ((a+b*t+c*t^2)*(-a+b*t+3*c*t^2)/(d*t^2)) t := by
  have hi : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have ha : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
  have hb : HasDerivAt (fun s : ℝ => b*s) b t := by simpa using hi.const_mul b
  have hc : HasDerivAt (fun s : ℝ => c*s^2) (c*(2*t)) t := by
    simpa using (hi.pow 2).const_mul c
  have hp : HasDerivAt (fun s : ℝ => a+b*s+c*s^2) (b+2*c*t) t := by
    convert! (ha.add hb).add hc using 1 <;> ring
  have hdv := (hp.pow 2).div ((hasDerivAt_id t).const_mul d) (mul_ne_zero hd ht)
  convert hdv.add_const e using 1
  all_goals first | (ext s; rfl) | (dsimp; field_simp; ring)
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (w uR qR : ℝ) (huR : 0 < uR) :
    (∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun s => PiHF k c s qR uR w)
        (-(c + uR * (qR - 3 * k * τ ^ 2 * uR + τ)) * (c + uR * (qR + τ * (k * τ * uR - 1)))
          / (4 * τ ^ 2 * uR)) τ) ∧
    (∀ τ : ℝ, 0 < τ →
      HasDerivAt (fun s => PiLF k c s qR uR w)
        (-(c + τ * uR * (qR + k * τ * uR - 1)) * (c - τ * uR * (qR + 3 * k * τ * uR - 1))
          / (4 * τ ^ 2 * uR)) τ) ∧
    HasDerivAt (fun s => PiHF k c s qR uR w)
      (-(c + uR * (qR - 3 * k * uR + 1)) * (c + uR * (qR + k * uR - 1)) / (4 * uR)) 1 ∧
    HasDerivAt (fun s => PiLF k c s qR uR w)
      (-(c + uR * (qR + k * uR - 1)) * (c - uR * (qR + 3 * k * uR - 1)) / (4 * uR)) 1 ∧
    (0 < qMHF k c 1 qR uR ↔ c + uR * (qR + k * uR - 1) < 0) := by
  have hd : 4*uR ≠ 0 := by positivity
  have hH (τ : ℝ) (hτ : 0 < τ) :
      HasDerivAt (fun s => PiHF k c s qR uR w)
        (-(c + uR * (qR - 3 * k * τ ^ 2 * uR + τ)) * (c + uR * (qR + τ * (k * τ * uR - 1)))
          / (4 * τ ^ 2 * uR)) τ := by
    convert ratio_deriv (c+uR*qR) (-uR) (k*uR^2) (4*uR)
      (qR*(w-k*uR^2)) τ hd (ne_of_gt hτ) using 1
    · ext s; unfold PiHF; ring
    · field_simp; ring
  have hL (τ : ℝ) (hτ : 0 < τ) :
      HasDerivAt (fun s => PiLF k c s qR uR w)
        (-(c + τ * uR * (qR + k * τ * uR - 1)) * (c - τ * uR * (qR + 3 * k * τ * uR - 1))
          / (4 * τ ^ 2 * uR)) τ := by
    convert ratio_deriv c (uR*(qR-1)) (k*uR^2) (4*uR)
      (qR*(w-k*uR^2)) τ hd (ne_of_gt hτ) using 1
    · ext s; unfold PiLF; ring
    · field_simp; ring
  refine ⟨hH, hL, ?_, ?_, ?_⟩
  · simpa only [one_pow, mul_one, one_mul, ← add_sub_assoc] using hH 1 (by norm_num)
  · simpa only [one_pow, mul_one, one_mul] using hL 1 (by norm_num)
  · simp only [qMHF, lt_max_iff, lt_self_iff_false, false_or, one_pow, mul_one]
    rw [div_pos_iff_of_pos_right (show 0 < 2*uR by positivity)]
    constructor <;> intro h <;> nlinarith








