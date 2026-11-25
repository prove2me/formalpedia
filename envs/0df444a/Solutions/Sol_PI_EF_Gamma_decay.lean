-- Prove2me | solution 1 for PI.EF.Gamma_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:07.325839+00:00
-- url     : https://prove2.me/submissions/a0ed905f-8ba9-49e4-9b48-ae7d33d26728

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Theorems.Thm_PI_EF_norm_twistedGamma
import Theorems.Thm_PI_EF_one_le_norm_add_one
import Theorems.Thm_PI_EF_norm_twistedGamma_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Set
namespace PI.EF
theorem _root_.solution {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) :
    ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * |w.im|) ≤ 3 * ‖w + 1‖ ^ 5 := by
  have key : ∀ v : ℂ, 1 / 2 ≤ v.re → v.re ≤ 11 / 2 →
      ‖Complex.Gamma v‖ * Real.exp (Real.pi / 2 * v.im) ≤ 3 * ‖v + 1‖ ^ 5 := by
    intro v a b
    have h := norm_twistedGamma_le a b
    rw [norm_twistedGamma, div_le_iff₀ (by
      have := one_le_norm_add_one (w := v) (by linarith)
      positivity)] at h
    exact h
  rcases le_total 0 w.im with hi | hi
  · rw [abs_of_nonneg hi]
    exact key w h1 h2
  · rw [abs_of_nonpos hi]
    have h := key ((starRingEnd ℂ) w) (by simpa using h1) (by simpa using h2)
    rw [Complex.Gamma_conj, Complex.norm_conj, Complex.conj_im] at h
    have e : ‖(starRingEnd ℂ) w + 1‖ = ‖w + 1‖ := by
      rw [← Complex.norm_conj (w + 1), map_add, map_one]
    rw [e] at h
    exact h
end PI.EF
