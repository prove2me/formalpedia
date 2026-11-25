-- Prove2me | solution 1 for P2M_GlobalTheory_CubeLift_pt_p__5876b0f23257
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:11.923265+00:00
-- url     : https://prove2.me/submissions/ef4d1082-1488-4a1d-b9ed-ecfed3ba4837

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective

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
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}
namespace GlobalTheory.CubeLift
theorem _root_.solution (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₂ = y := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp
end GlobalTheory.CubeLift
