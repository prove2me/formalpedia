-- Prove2me | solution 1 for PI.RhsWLim.W.opAct_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:43.585922+00:00
-- url     : https://prove2.me/submissions/7a754c27-58cf-4a0d-b75c-fc123101fcf0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_embWb_wI
import Theorems.Thm_PI_RhsWLim_W_sum_wb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    opAct k r (embWb k r μ) p = blkAct k μ p := by
  have key : ∀ j : Fin (k + 1), (embWb k r μ *ᵥ opVec k r p) (wI k r j) = (μ *ᵥ toW k p) j := by
    intro j
    have hv : ∀ m : Fin (k + 1), opVec k r p (wI k r m) = toW k p m := by
      intro m
      have := m.isLt
      unfold opVec toW wI
      by_cases h : m.val < k
      · rw [dif_pos (by simp only; omega), dif_pos h]
        exact congrArg p.1 (Fin.ext (by simp))
      · rw [dif_neg (by simp only; omega), dif_neg h, if_pos (by simp only; omega)]
    show ∑ i, embWb k r μ (wI k r j) i * opVec k r p i = ∑ m, μ j m * toW k p m
    rw [sum_wb]
    · exact Finset.sum_congr rfl fun m _ => by rw [embWb_wI, hv]
    · intro i hi
      have : opVec k r p i = 0 := by
        unfold opVec
        rw [dif_neg (by omega), if_neg (by omega)]
      rw [this, mul_zero]
  unfold opAct opCo blkAct ofW
  ext i
  · exact key _
  · exact key _
end PI.RhsWLim.W
