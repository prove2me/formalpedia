-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.nset_isMatGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:30.545487+00:00
-- url     : https://prove2.me/submissions/08670794-be21-4fb2-973a-21d610b9943b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsCompactInterUnitBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_NonstandardUnimodularLattice
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isClosed_N
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_inv_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nilpotent_subgroup


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
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
namespace PI.NUnimodLoc.UnitaryGroupMassFormula
theorem _root_.solution (k r : ℕ) : IsMatGroup (Nset k r) :=
  ⟨isClosed_N, (nilpotent_subgroup k r).1, (nilpotent_subgroup k r).2.1,
    fun a ha => ⟨(nilpotent_subgroup k r).2.2 a ha, mul_inv_UH ha.1⟩⟩
end PI.NUnimodLoc.UnitaryGroupMassFormula
