-- Prove2me | solution 1 for PI.EF.mem_ball_ctr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:03.667806+00:00
-- url     : https://prove2.me/submissions/7e25605b-f0b3-4dea-a2c6-2d7aa3437160

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
import Theorems.Thm_PI_EF_ctr_im
import Theorems.Thm_PI_EF_ctr_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_im
attribute [local simp] PI.EF.ctr_re



set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) :
    s ∈ closedBall (ctr s.im) (5 / 2) := by
  rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
  have h : s - (2 + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith
end PI.EF
