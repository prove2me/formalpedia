-- Prove2me | solution 1 for P2M_GlobalTheory_AbCoh__Two_apply_63110fbf2b67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:09:49.786603+00:00
-- url     : https://prove2.me/submissions/b041b822-f587-43e3-952d-a374802cae25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalOneFormFrameCoordinatesConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumCupOneFormsZeroImpCoordinatesZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2GeneratedByCupsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumWedgeGlobalOneFormsEqZeroIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareKerOfSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2ExteriorSquareIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
namespace GlobalTheory.AbCoh
theorem _root_.solution (a b : M) : ιTwo a b = exteriorPower.ιMulti R 2 ![a, b] := by
  rw [ιTwo, LinearMap.mk₂_apply]
end GlobalTheory.AbCoh
