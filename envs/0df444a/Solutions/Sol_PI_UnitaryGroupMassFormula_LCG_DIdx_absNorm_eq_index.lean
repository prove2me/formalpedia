-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DIdx.absNorm_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:34:24.033175+00:00
-- url     : https://prove2.me/submissions/2b10f145-cb0d-4c98-b8da-0e6de483eb8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DIdx
namespace PI.UnitaryGroupMassFormula.LCG.DIdx
theorem _root_.solution {S : Type} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) : Ideal.absNorm I = I.toAddSubgroup.index := rfl
end PI.UnitaryGroupMassFormula.LCG.DIdx
