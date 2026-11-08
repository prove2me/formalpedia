-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:48.1662+00:00
-- url     : https://prove2.me/submissions/2b1baf97-6f4b-46f8-adac-2e2f0ff06e40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_components
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    [H.FiniteIndex] (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) :
    (volume : Measure ℍ) (lpsCosetSectionDomain H r) =
      (H.index : ℝ≥0∞) * volume ModularGroup.fd := by
  let : Fintype (lpsEffectiveModularGroup ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsCosetSectionDomain
  rw [measure_iUnion₀ (lpsCosetSectionDomain_components H r hr)
    (fun c => lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (r c)⁻¹)]
  simp only [measure_smul,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Subgroup.index, Nat.card_eq_fintype_card]
end QEC.Coding.TannerLiftedProduct
