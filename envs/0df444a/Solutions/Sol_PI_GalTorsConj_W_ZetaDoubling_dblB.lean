-- Prove2me | solution 1 for PI.GalTorsConj.W.ZetaDoubling.dblB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:43.696379+00:00
-- url     : https://prove2.me/submissions/89536b64-4324-4083-be1f-336b8656b277

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_derivWeierstrassP_ne_zero
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_dblA
import Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_dbl_alg

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
open Filter Topology
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd
namespace PI.GalTorsConj.W.ZetaDoubling
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) = dblX (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂ := by
  rw [dblA L hz h2]
  exact dbl_alg _ _ _ (derivWeierstrassP_ne_zero L hz h2)
end PI.GalTorsConj.W.ZetaDoubling
