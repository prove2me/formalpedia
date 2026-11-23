-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.hasDerivAt_wp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:59.314312+00:00
-- url     : https://prove2.me/submissions/55a4727a-0ebc-4abb-a73b-cf1ba8b7d6c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw

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
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have h := ((L.analyticOnNhd_weierstrassP z hz).differentiableAt).hasDerivAt
  rwa [PeriodPair.deriv_weierstrassP] at h
end PI.GalTorsConj.W.OriginCoordinatesAdd
