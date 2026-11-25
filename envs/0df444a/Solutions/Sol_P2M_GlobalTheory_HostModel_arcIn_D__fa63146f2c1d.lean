-- Prove2me | solution 1 for P2M_GlobalTheory_HostModel_arcIn_D__fa63146f2c1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:29:01.323184+00:00
-- url     : https://prove2.me/submissions/2c164029-0876-4735-8009-daa0f1a9cc10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData ConjDual
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {l : Level H} (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k)
namespace GlobalTheory.HostModel
theorem _root_.solution : (arcIn c k bF).D₀ = toricPre k (𝓞 E) fun _ => 1 := rfl
end GlobalTheory.HostModel
