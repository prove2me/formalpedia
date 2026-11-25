-- Prove2me | solution 1 for P2M_GlobalTheory_SW_LagRep_ccT_mul__96963e977bb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:11.464411+00:00
-- url     : https://prove2.me/submissions/6d469c28-ef9e-4ed8-9648-9556277fc0c6

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
theorem _root_.solution {α β δ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β δ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]
end GlobalTheory.SW.LagRep
