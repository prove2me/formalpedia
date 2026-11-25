-- Prove2me | solution 1 for P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__eq_iff_acb49a50f83f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:47:23.111206+00:00
-- url     : https://prove2.me/submissions/607f6ae7-f2ad-48b2-8013-7857ce05af77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Theorems.Thm_P2M_PI_QuotSetU_UnitaryGroupMassFormula_h__h__cabeda697d55

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution (k r : ℕ) (i j : Fin (2 * r + k + 1)) : i = hσ k r j ↔ j = hσ k r i := by
  constructor
  · rintro rfl
    exact (hσ_hσ k r j).symm
  · rintro rfl
    exact (hσ_hσ k r i).symm
end PI.QuotSetU.UnitaryGroupMassFormula
