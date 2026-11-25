-- Prove2me | solution 1 for PI.RhsWLim.W.form_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:44.091815+00:00
-- url     : https://prove2.me/submissions/e5c2d8cd-db2d-4341-b831-f2a9ecbff87a

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
theorem _root_.solution (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    (Aᴴ * Hb k * A) i j = ∑ l : Fin k, conj (A l.castSucc i) * A l.castSucc j -
      conj (A (Fin.last k) i) * A (Fin.last k) j := by
  rw [Hb, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def, Fin.castSucc_ne_last, if_false,
    if_true, mul_one]
  ring
end PI.RhsWLim.W
