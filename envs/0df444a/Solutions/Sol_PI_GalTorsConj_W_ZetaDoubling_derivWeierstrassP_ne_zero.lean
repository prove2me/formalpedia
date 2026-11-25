-- Prove2me | solution 1 for PI.GalTorsConj.W.ZetaDoubling.derivWeierstrassP_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:50.841817+00:00
-- url     : https://prove2.me/submissions/d84b97ae-1599-4013-b9c5-4aead7067566

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Theorems.Thm_Formalism_L2_Th1_F_pDerivZero


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
    L.derivWeierstrassP z ≠ 0 := by
  intro h
  exact h2 ((pDerivZero L z hz).1 h)
end PI.GalTorsConj.W.ZetaDoubling
