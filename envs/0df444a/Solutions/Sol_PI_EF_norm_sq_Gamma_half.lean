-- Prove2me | solution 1 for PI.EF.norm_sq_Gamma_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:40.475982+00:00
-- url     : https://prove2.me/submissions/a2473adf-80a0-4b2b-a1e5-d581180c810b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma

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
theorem _root_.solution (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := 1 / 2 + t * I with hz
  have hconj : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext
    · simp [hz]; norm_num
    · simp [hz]
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at h
  have hs : Complex.sin (Real.pi * z) = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    have e : (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi / 2 := by
      rw [hz]; push_cast; ring
    rw [e, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hs] at h
  have h' : normSq (Complex.Gamma z) = Real.pi / Real.cosh (Real.pi * t) := by exact_mod_cast h
  rw [← h', Complex.normSq_eq_norm_sq]
end PI.EF
