-- Prove2me | solution 1 for P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:18.867696+00:00
-- url     : https://prove2.me/submissions/89ee4e49-08ab-4f77-bc80-642f859a9412

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (c : R) (s : SecOver π (LB.LinComb L φ ε)) :
    sval (c • s : SecOver π _) r z J = constVal (r ≫ π) z c * sval s r z J :=
  gs_smul π r z _ (hJ.mem φ r) c _
end GlobalTheory.FieldBaseChange
