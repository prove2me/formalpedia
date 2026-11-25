-- Prove2me | solution 1 for PI.NglqJacSplitW.modF_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:20.008935+00:00
-- url     : https://prove2.me/submissions/687b11cb-9f45-4ef5-ac38-d2dc158807d1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Theorems.Thm_PI_NglqJacSplitW_modF_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]
namespace PI.NglqJacSplitW
theorem _root_.solution {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : modF F (a * b) = modF F a * modF F b := by
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb,
    show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]
  push_cast
  rfl
end PI.NglqJacSplitW
