-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.wp_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:33:21.684394+00:00
-- url     : https://prove2.me/submissions/f4d19c4b-0538-42be-9da7-f3805dab800b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Theorems.Thm_Formalism_L2_Th1_F_pInjective


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
    L.weierstrassP z - L.weierstrassP w ≠ 0 := by
  intro h
  rcases (pInjective L z w hz hw).1 (sub_eq_zero.1 h) with h' | h'
  · exact hm h'
  · exact hp h'
end PI.GalTorsConj.W.OriginCoordinatesAdd
