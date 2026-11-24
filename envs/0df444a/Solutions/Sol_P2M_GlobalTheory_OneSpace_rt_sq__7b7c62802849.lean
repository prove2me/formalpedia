-- Prove2me | solution 1 for P2M_GlobalTheory_OneSpace_rt_sq__7b7c62802849
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:04.895061+00:00
-- url     : https://prove2.me/submissions/6af7870a-17c2-48e8-a928-62c70af5c08c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.OneSpace
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OneSpace
theorem _root_.solution (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using this
end GlobalTheory.OneSpace
