-- Prove2me | solution 1 for PI.EF.Loc.norm_logDeriv_refl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:17.715457+00:00
-- url     : https://prove2.me/submissions/b3388fd7-4bee-42c5-bcfe-2914377c0d4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Theorems.Thm_PI_EF_Loc_le_norm_refl
import Theorems.Thm_PI_EF_Loc_hasDerivAt_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate
namespace PI.EF.Loc
theorem _root_.solution {s₀ ρ z : ℂ} {R R' : ℝ} (hR'R : R' < R) (hR : 0 < R)
    (hρ : ρ ∈ closedBall s₀ R') (hz : z ∈ closedBall s₀ R) :
    ‖logDeriv (refl s₀ R ρ) z‖ ≤ R' / (R * (R - R')) := by
  have hpos : 0 < R - R' := sub_pos.mpr hR'R
  have hl := le_norm_refl hR hρ hz
  have hn : 0 < ‖refl s₀ R ρ z‖ := lt_of_lt_of_le hpos hl
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  rw [logDeriv_apply, (hasDerivAt_refl s₀ R ρ z).deriv, norm_div, norm_div, norm_neg, mul_one,
    Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le, div_div,
    div_le_div_iff₀ (mul_pos hR hn) (mul_pos hR hpos)]
  have h4 := mul_le_mul ha hl hpos.le ((norm_nonneg _).trans ha)
  nlinarith
end PI.EF.Loc
