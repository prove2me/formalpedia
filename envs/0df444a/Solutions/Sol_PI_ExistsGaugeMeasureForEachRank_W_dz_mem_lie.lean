-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.dz_mem_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:41.46018+00:00
-- url     : https://prove2.me/submissions/0b202b86-20bf-443d-b9c9-7fc01d2bc2ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_exp_dz
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_smul_dz
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conj_mul_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (s : ℝ) : dz r ((s : ℂ) * Complex.I) ∈ lieOf (UWb 0 r) := by
  intro t
  rw [smul_dz, exp_dz]
  apply dgl_mem
  rw [conj_mul_iff, Complex.norm_exp]
  simp
end PI.ExistsGaugeMeasureForEachRank.W
