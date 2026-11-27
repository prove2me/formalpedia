-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:24:21.206744+00:00
-- url     : https://prove2.me/submissions/8a76ca5e-c74c-49e4-8c2e-b9e497b15c93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_QForm_QVal_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_genHasVal_pullGen_of


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
theorem _root_.solution (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : Q (-χ) = Q χ := by
  have hL := D.toPre.P.isLB
  have hsym := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ D.toPre.sym D.toPre.sym_gen (D.toPre.c χ).left (D.toPre.xK χ)
    (ptK_eq D.toPre χ)
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (-χ)) hsym
  have := QVal_unique hϖ D
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _ (by (simp [Sum.forall, Fin.forall_fin_succ, Over.w, Over.w_assoc, eSec, Matrix.cons_val_zero, Matrix.cons_val_succ])) (by (simp [Sum.forall, Fin.forall_fin_succ, Over.w, Over.w_assoc, eSec, Matrix.cons_val_zero, Matrix.cons_val_succ])) _ _ (D.toPre.psi_gen χ) (D.psi_even χ) h1) (hQ χ)
  linarith
end ReciprocityTheory.ChartRestriction.G.DVR.QForm
