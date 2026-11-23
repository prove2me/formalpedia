-- Prove2me | solution 1 for PI.EF.norm_sub_ctr_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:53.661336+00:00
-- url     : https://prove2.me/submissions/316b9e22-e6ba-41fe-babf-7fbe97fd55de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
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
theorem _root_.solution (ρ : ℂ) (t : ℝ) : ‖ρ - ctr t‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ctr_re, ctr_im]
  ring
end PI.EF
