-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_mk__chartIdeal_X_self_6bdb4b0af909
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:58.327305+00:00
-- url     : https://prove2.me/submissions/8669255c-25cf-446b-bad5-b92957377ff0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mk_chartIdeal_X_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, j k⟩) = 1 :=
  mk_chartIdeal_X_self V j k
end ReciprocityTheory.ChartRestriction.G.AI.I1
