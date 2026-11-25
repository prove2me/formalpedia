-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.chartSwap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:29.236792+00:00
-- url     : https://prove2.me/submissions/ab5c200e-9e14-4a5d-8d5a-7b8f97770ec1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_mk__chartIdeal_X_self_6bdb4b0af909
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AI_I1_chartSwap_mk__4f83fe97b485

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
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩)))
    (hv : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V i) (X ⟨k, j k⟩))) :
    (chartSwap hV j i hv).comp (chartSwap hV i j hu) = AlgHom.id F _ := by
  refine Ideal.Quotient.algHom_ext F (MvPolynomial.algHom_ext fun p => ?_)
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [chartSwap_mkₐ, map_mul, chartSwap_mkₐ]
  have hui : chartSwap hV j i hv (↑(hu p.1).unit) = ↑(hv p.1).unit⁻¹ := by
    rw [(hu p.1).unit_spec, chartSwap_mkₐ, mkₐ_chartIdeal_X_self, mul_one]
  have hinv : chartSwap hV j i hv (↑(hu p.1).unit⁻¹) = ↑(hv p.1).unit := by
    have h1 : chartSwap hV j i hv (↑(hu p.1).unit⁻¹) * chartSwap hV j i hv (↑(hu p.1).unit) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hui] at h1
    exact Units.mul_inv_eq_one.mp h1
  rw [hinv, Units.mul_inv_cancel_left]
end ReciprocityTheory.ChartRestriction.G.AI.I1
