-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_mk__4f83fe97b485
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:13.04502+00:00
-- url     : https://prove2.me/submissions/5a4ecc54-a99c-47d6-9fdc-c6b1df831f9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim

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
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩))) (p : Σ k, ι k) :
    chartSwap hV i j hu (Ideal.Quotient.mkₐ F (chartIdeal V i) (X p)) =
      ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p) := by
  unfold chartSwap
  exact (Ideal.Quotient.liftₐ_apply _ _ _ _).trans ((Ideal.Quotient.lift_mk _ _ _).trans (aeval_X _ _))
end ReciprocityTheory.ChartRestriction.G.AI.I1
