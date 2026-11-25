-- Prove2me | solution 1 for P2M_GlobalTheory_SharpWeil_zpow_sum__176ec8fcdc9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:38.291348+00:00
-- url     : https://prove2.me/submissions/5438d72e-fa66-4d56-95a7-e56dcf1ec12c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CommutatorPairingE8SharpLevelPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpWeil
variable {G C : Type} [CommGroup G] [CommGroup C] {k : ℕ}
namespace GlobalTheory.SharpWeil
theorem _root_.solution {I : Type} (s : Finset I) (ζ : C) (a : I → ℤ) : ζ ^ (∑ i ∈ s, a i) = ∏ i ∈ s, ζ ^ a i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
end GlobalTheory.SharpWeil
