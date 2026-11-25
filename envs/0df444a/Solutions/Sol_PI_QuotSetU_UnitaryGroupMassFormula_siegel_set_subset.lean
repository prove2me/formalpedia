-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.siegel_set_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:19.342201+00:00
-- url     : https://prove2.me/submissions/87ce9016-29c0-4689-9478-2d52a658f295

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_uh_mul

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
theorem _root_.solution : SsetSub := by
  intro k r z s hsx
  rw [Sset.eq_1, Set.mem_setOf_eq] at hsx
  obtain ⟨h, hh, m, hm, rfl⟩ := hsx
  rw [UWset.eq_1, Set.mem_setOf_eq] at hh
  rw [Nset.eq_1, Set.mem_setOf_eq] at hm
  exact uh_mul hh.1 hm.1
end PI.QuotSetU.UnitaryGroupMassFormula
