-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:22:35.096375+00:00
-- url     : https://prove2.me/submissions/ed95ccbe-bb86-45ec-9dc0-8628cc3bf3fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_ge_of_in


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V))
variable {Q : D.toPre.X → ℤ}
include hϖ
namespace ReciprocityTheory.ChartRestriction.G.DVR.QForm
theorem _root_.solution (hQ : IsQ D.toPre ϖ Q) {χ : D.toPre.X} (hχ : χ ≠ 0) : 1 ≤ Q χ := by
  have h := genHasVal_ge_of_in hϖ D.toPre.P.L D.toPre.P.isLB (D.toPre.c χ).left (D.toPre.xK χ) (ptK_eq D.toPre χ)
    (-1) (D.toPre.psi χ) 1 (fun j W hW hle h => by rw [pow_one]; exact D.psi_pos χ hχ j W hW hle h) (hQ χ)
  exact_mod_cast h
end ReciprocityTheory.ChartRestriction.G.DVR.QForm
