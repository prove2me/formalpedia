-- Prove2me | solution 1 for PI.GalTorsConj.W.wp_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:58.4758+00:00
-- url     : https://prove2.me/submissions/ae58a7e2-e58b-41fc-a4da-8fb84f85bb9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution (L : PeriodPair) (z : ℂ) {ω : ℂ} (h : ω ∈ L.lattice) :
    L.weierstrassP (z + ω) = L.weierstrassP z := PeriodPair.weierstrassP_add_coe L z ⟨ω, h⟩
end PI.GalTorsConj.W
