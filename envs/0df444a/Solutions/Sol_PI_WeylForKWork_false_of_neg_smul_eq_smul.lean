-- Prove2me | solution 1 for PI.WeylForKWork.false_of_neg_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:01.057852+00:00
-- url     : https://prove2.me/submissions/7b2000b9-73b2-45c3-9464-5d51ce571c87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace
namespace PI.WeylForKWork
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (z : ℂ) (hz : z ≠ 0)
    (w : H) (hw : w ≠ 0) (h : (z * -1) • w = z • w) : False := by
  have e3 := sub_eq_zero.mpr h
  rw [← sub_smul, smul_eq_zero] at e3
  rcases e3 with h' | h'
  · apply hz; linear_combination (-1/2 : ℂ) * h'
  · exact hw h'
end PI.WeylForKWork
