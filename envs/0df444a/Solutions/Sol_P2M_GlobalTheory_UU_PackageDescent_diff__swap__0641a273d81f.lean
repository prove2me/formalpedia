-- Prove2me | solution 1 for P2M_GlobalTheory_UU_PackageDescent_diff__swap__0641a273d81f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:07.077588+00:00
-- url     : https://prove2.me/submissions/47c3523d-ac10-40a9-82bf-9de576dd6bc7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough

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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G B : Over S} (q : G ⟶ B) [Flat q.left] [Surjective q.left]
variable [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] [IsMonHom q] [QuasiCompact q.left]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] (W : A → U) (a b d : A) :
    diff₃ W a b d = diff₃ W b a d := by
  rw [diff₃, diff₃, mul_comm b a]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.UU.PackageDescent
