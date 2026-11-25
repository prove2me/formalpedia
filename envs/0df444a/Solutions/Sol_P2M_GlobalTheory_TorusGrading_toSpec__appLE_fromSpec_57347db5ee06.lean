-- Prove2me | solution 1 for P2M_GlobalTheory_TorusGrading_toSpec__appLE_fromSpec_57347db5ee06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:40.739388+00:00
-- url     : https://prove2.me/submissions/85a3fdd3-76bc-4af2-b9a7-9e285c451757

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorusGrading
namespace GlobalTheory.TorusGrading
theorem _root_.solution {Y Z : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (g : Z ⟶ Y)
    (h : ⊤ ≤ g ⁻¹ᵁ V) : Z.toSpecΓ ≫ Spec.map (g.appLE V ⊤ h) ≫ hV.fromSpec = g := by
  have : IsIso (⊤ : Z.Opens).ι := inferInstanceAs (IsIso Z.topIso.hom)
  rw [← cancel_epi (⊤ : Z.Opens).ι, ← Category.assoc, ← Scheme.Opens.toSpecΓ_top,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
end GlobalTheory.TorusGrading
