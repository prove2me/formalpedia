-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.dgl_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:25:36.090078+00:00
-- url     : https://prove2.me/submissions/f7d98801-52c3-435a-8127-50da5d26d3c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_rev_eq_c_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Hpk_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution {u : ℂ} (h : dgl r u ∈ UWb 0 r) : (starRingEnd ℂ) u * u = 1 := by
  have hU : (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r := h.1
  have h1 := congrFun (congrFun hU (cI r)) (cI r)
  have hc : Fin.rev (cI r) = cI r := (rev_eq_c_iff (cI r)).2 rfl
  simp only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Pi.star_apply, if_true] at h1
  rw [Hpk_apply] at h1
  simp only [hc, if_true] at h1
  show (starRingEnd ℂ) u * u = 1
  rw [show (starRingEnd ℂ) u = star u from rfl]
  linear_combination -h1
end PI.ExistsGaugeMeasureForEachRank.W
