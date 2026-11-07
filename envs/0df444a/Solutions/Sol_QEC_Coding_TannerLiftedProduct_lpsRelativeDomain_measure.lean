-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:16.685017+00:00
-- url     : https://prove2.me/submissions/d2482b76-9cb9-4ad0-babb-8b38760a8fb1

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_components

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open MeasureTheory Set Filter
open scoped Pointwise ENNReal
noncomputable section
variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_countableQuotient
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup G) (s : Set α)
    [H.FiniteIndex] (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    (μ : Measure α) (lpsRelativeDomain H s r) =
      (H.index : ℝ≥0∞) * μ s := by
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsRelativeDomain
  rw [measure_iUnion₀ (lpsRelativeDomain_components H s r hr hs)
    (fun c => hs.nullMeasurableSet_smul (r c)⁻¹)]
  simp only [measure_smul,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Subgroup.index, Nat.card_eq_fintype_card]
end QEC.Coding.TannerLiftedProduct
