-- Prove2me | solution 1 for PI.RhsWLim.W.emb_mulVec_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:47.391986+00:00
-- url     : https://prove2.me/submissions/b9f7794b-672b-4f0f-81aa-ee0689265b29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW

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
open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) : (embWb k r μ *ᵥ v) i = v i := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · unfold embWb
    rw [dif_neg (by omega), if_pos ⟨rfl, by omega⟩, one_mul]
  · intro l _ hl
    unfold embWb
    rw [dif_neg (by omega), if_neg (fun h => hl h.1.symm), zero_mul]
  · simp
end PI.RhsWLim.W
