-- Prove2me | solution 1 for PI.GalTorsConj.W.dblX_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:23.200028+00:00
-- url     : https://prove2.me/submissions/cc8e0c4e-4f51-4b22-a525-1329ead03cd2

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
    φ (dblX x y g) = dblX (φ x) (φ y) (φ g) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]
end PI.GalTorsConj.W
