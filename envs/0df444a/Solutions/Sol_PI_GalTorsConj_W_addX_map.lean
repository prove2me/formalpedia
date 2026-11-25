-- Prove2me | solution 1 for PI.GalTorsConj.W.addX_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:39.899804+00:00
-- url     : https://prove2.me/submissions/f2334cb0-3ae3-483d-bd92-eb165553ed81

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
variable {K K' : Type*} [Field K] [Field K']
namespace PI.GalTorsConj.W
theorem _root_.solution (φ : K →+* K') (x y x₂ y₂ : K) :
    φ (addX x y x₂ y₂) = addX (φ x) (φ y) (φ x₂) (φ y₂) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]
end PI.GalTorsConj.W
