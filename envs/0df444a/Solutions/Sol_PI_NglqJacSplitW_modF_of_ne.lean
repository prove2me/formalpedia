-- Prove2me | solution 1 for PI.NglqJacSplitW.modF_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:01.485078+00:00
-- url     : https://prove2.me/submissions/df315f76-ee43-43f3-b812-bb7db25c5155

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeNGLQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_DiscreteHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete

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
theorem _root_.solution {a : F} (h : a ≠ 0) :
    modF F a = ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞) := by
  rw [modF, dif_neg h]
end PI.NglqJacSplitW
