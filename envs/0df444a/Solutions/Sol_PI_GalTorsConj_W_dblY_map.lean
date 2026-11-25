-- Prove2me | solution 1 for PI.GalTorsConj.W.dblY_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:34.189829+00:00
-- url     : https://prove2.me/submissions/c3af07d9-7c96-4824-9cad-a2584836443f

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
theorem _root_.solution (φ : K →+* K') (x y g : K) :
    φ (dblY x y g) = dblY (φ x) (φ y) (φ g) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]
end PI.GalTorsConj.W
