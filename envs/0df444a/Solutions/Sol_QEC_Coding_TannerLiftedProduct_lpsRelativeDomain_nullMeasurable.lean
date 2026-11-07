-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_nullMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:04:05.493208+00:00
-- url     : https://prove2.me/submissions/415e7521-a5b9-4b1d-be04-bcd440bbd4a2

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain

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
    (r : G ⧸ H → G) (hs : IsFundamentalDomain G s μ) :
    NullMeasurableSet (lpsRelativeDomain H s r) μ := by
  apply NullMeasurableSet.iUnion
  intro c
  exact hs.nullMeasurableSet_smul (r c)⁻¹
end QEC.Coding.TannerLiftedProduct
