-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:18.735329+00:00
-- url     : https://prove2.me/submissions/61bdbf75-6945-4d79-ac5b-a5323cec71ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_wp_ne
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_stepA
import Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_chord_alg

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
theorem _root_.solution (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hm : z - w ∉ L.lattice) (hp : z + w ∉ L.lattice) :
    L.weierstrassP (z + w) = addX (L.weierstrassP z) (L.derivWeierstrassP z)
        (L.weierstrassP w) (L.derivWeierstrassP w) := by
  rw [stepA L hz hw hm hp]
  exact chord_alg _ _ _ _ L.g₂ L.g₃ (wp_ne L hz hw hm hp) (L.derivWeierstrassP_sq z hz)
    (L.derivWeierstrassP_sq w hw)
end PI.GalTorsConj.W.OriginCoordinatesAdd
