-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:52.139112+00:00
-- url     : https://prove2.me/submissions/1bae8be2-e07c-45bd-8031-ccf17664ac6b

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_nullMeasurable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_covers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_aedisjoint

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
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (lpsRelativeDomain H s r) μ := by
  apply IsFundamentalDomain.mk'' (lpsRelativeDomain_nullMeasurable H s r hs)
  · exact lpsRelativeDomain_covers H s r hr hs
  · exact lpsRelativeDomain_aedisjoint H s r hr hs
  · intro h
    exact (MeasureTheory.measurePreserving_smul (h : G) μ).quasiMeasurePreserving
end QEC.Coding.TannerLiftedProduct
