-- Prove2me | solution 1 for P2M_GlobalTheory_SW_LagRep_ccT_ccT__22e929649a54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:30:43.578492+00:00
-- url     : https://prove2.me/submissions/786d69ef-b728-429b-b6bc-0861b5400b98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LagRep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.LagRep
theorem _root_.solution {α β : Type} (A : Matrix α β E) : ccT (ccT A) = A := by
  ext i j
  simp [ccT, cc]
end GlobalTheory.SW.LagRep
