-- Prove2me | solution 1 for PI.GalTorsConj.W.pNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:18.334668+00:00
-- url     : https://prove2.me/submissions/226c6140-49d7-41a7-b53a-d797c6ef74b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_StAddRight
import Theorems.Thm_PI_GalTorsConj_W_pInj

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
theorem _root_.solution (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w) (hy : L.derivWeierstrassP z = -L.derivWeierstrassP w) :
    z + w ∈ L.lattice := by
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using L.lattice.neg_mem h)
  have h := pInj L hz hw' (by rw [PeriodPair.weierstrassP_neg, hx])
    (by rw [PeriodPair.derivWeierstrassP_neg, hy])
  simpa using h
end PI.GalTorsConj.W
