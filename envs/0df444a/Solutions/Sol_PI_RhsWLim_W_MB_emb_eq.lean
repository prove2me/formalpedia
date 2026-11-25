-- Prove2me | solution 1 for PI.RhsWLim.W.MB.emb_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:20.107915+00:00
-- url     : https://prove2.me/submissions/9b0b2051-c892-4398-96a0-39743e941a70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_wI_midx
import Theorems.Thm_PI_RhsWLim_W_MB_emb_out_col
import Theorems.Thm_PI_RhsWLim_W_MB_emb_out_row
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mid
import Theorems.Thm_PI_RhsWLim_W_MB_Em_mul_mid
import Theorems.Thm_PI_RhsWLim_W_MB_Em_mul_out
import Theorems.Thm_PI_RhsWLim_W_MB_mul_EmT_mid
import Theorems.Thm_PI_RhsWLim_W_MB_mul_EmT_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.MB
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hj : mid k r j
  · rw [mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]
    by_cases hi : mid k r i
    · rw [Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero]
    · rw [Em_mul_out _ i _ hi, emb_out_row μ i j hi]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]
  · rw [mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]
    ring
end PI.RhsWLim.W.MB
