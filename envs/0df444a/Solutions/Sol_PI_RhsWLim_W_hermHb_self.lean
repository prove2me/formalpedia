-- Prove2me | solution 1 for PI.RhsWLim.W.hermHb_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:33.823389+00:00
-- url     : https://prove2.me/submissions/adbbc980-af5f-4992-9e69-34c4ab6260b5

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
theorem _root_.solution (v : Fin (k + 1) → ℂ) :
    herm (Hb k) v v = ((∑ l : Fin k, Complex.normSq (v l.castSucc) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  unfold herm
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [Hb, Matrix.mulVec_diagonal, Fin.castSucc_ne_last, if_false, if_true, Pi.star_apply, Complex.star_def]
  push_cast [Complex.normSq_eq_conj_mul_self]
  ring
end PI.RhsWLim.W
