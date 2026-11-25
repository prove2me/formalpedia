-- Prove2me | solution 1 for PI.EF.PK.hor_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:59.590805+00:00
-- url     : https://prove2.me/submissions/9132d4b1-bc23-4090-83d1-752c45d850be

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
import Theorems.Thm_PI_EF_PK_seg_bound
import Theorems.Thm_PI_EF_PK_norm_upow_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (G : ℂ → ℂ) (u c T' A h : ℝ) (hu : 1 ≤ u) (hc : -1 / 2 ≤ c) (hT'0 : 0 < T')
    (hA : 0 ≤ A) (hh : |h| = T') (hb : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ c → ‖G ((σ : ℂ) + h * I)‖ ≤ A) :
    ‖∫ x : ℝ in (-1 / 2)..c, G ((x : ℂ) + h * I) * ((u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I))‖ ≤
      A * (u ^ c / T') * (c - -1 / 2) := by
  refine seg_bound _ _ _ _ hc (fun x hx1 hx2 => ?_)
  rw [norm_mul]
  have h1 := hb x hx1 hx2
  have him : |h| ≤ ‖(x : ℂ) + h * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
    simpa using this
  have h2 : ‖(u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I)‖ ≤ u ^ c / T' :=
    norm_upow_div u hu _ c T' hT'0 (by simpa using hx2) (by rw [← hh]; exact him)
  exact mul_le_mul h1 h2 (norm_nonneg _) hA
end PI.EF.PK
