-- Prove2me | solution 1 for P2M_GlobalTheory_UT_OLinEnd_prod_O__7772f5470651
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:17.288383+00:00
-- url     : https://prove2.me/submissions/d738d9ef-05eb-4de6-bbfb-4e69aa844494

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.OLinEnd
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.UT.OLinEnd
theorem _root_.solution (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (D.Oφ p χ i) ^ Oε i =
      h (cP D T χ * p).left * (h (cP D T χ).left)⁻¹ * (h p.left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  rw [Fin.prod_univ_four, _root_.mul_comm (cP D T χ) p]
  show h (p * cP D _ χ).left ^ (1 : ℤ) * h (cP D _ χ).left ^ (-1 : ℤ) * h p.left ^ (-1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]
end GlobalTheory.UT.OLinEnd
