-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.hasDerivAt_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:39.785621+00:00
-- url     : https://prove2.me/submissions/e03c0d10-bcc3-4841-8d03-a8792b54b8c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_wp
import Theorems.Thm_Formalism_L2_Th1_F_pSecond


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
open PI.GalTorsConj.W.OriginCoordinatesAdd
namespace PI.GalTorsConj.W.OriginCoordinatesAdd
theorem _root_.solution (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice)
    (hne : L.weierstrassP z - L.weierstrassP w ≠ 0) :
    HasDerivAt (lam L w)
      (((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w)
        - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z)
        / (L.weierstrassP z - L.weierstrassP w) ^ 2) z := by
  have h1 : HasDerivAt (fun z' => L.derivWeierstrassP z' - L.derivWeierstrassP w)
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := (pSecond L z hz).sub_const _
  have h2 : HasDerivAt (fun z' => L.weierstrassP z' - L.weierstrassP w)
      (L.derivWeierstrassP z) z := (hasDerivAt_wp L hz).sub_const _
  exact h1.div h2 hne
end PI.GalTorsConj.W.OriginCoordinatesAdd
