-- Prove2me | solution 1 for PI.GalTorsConj.W.OriginCoordinatesAdd.chord_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:48.068354+00:00
-- url     : https://prove2.me/submissions/d6729dc4-cc31-4df5-a5a7-ef8771df6d84

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
theorem _root_.solution (x y x₂ y₂ g g' : ℂ) (hd : x - x₂ ≠ 0)
    (hy : y ^ 2 = 4 * x ^ 3 - g * x - g') (hy₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g * x₂ - g') :
    x - ((6 * x ^ 2 - g / 2) * (x - x₂) - (y - y₂) * y) / (x - x₂) ^ 2 / 2
      = addX x y x₂ y₂ := by
  unfold addX
  field_simp
  linear_combination 4 * hy - 4 * hy₂
end PI.GalTorsConj.W.OriginCoordinatesAdd
