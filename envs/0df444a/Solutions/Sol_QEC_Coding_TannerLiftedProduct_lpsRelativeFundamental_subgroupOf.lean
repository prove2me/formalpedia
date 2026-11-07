-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeFundamental_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:26.870525+00:00
-- url     : https://prove2.me/submissions/05cd76b7-a7aa-4f11-99ba-842454aae684

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
theorem _root_.solution {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] (H K : Subgroup G) (h : H ≤ K) {μ : Measure α}
    {s : Set α} (hs : IsFundamentalDomain (H.subgroupOf K) s μ) :
    IsFundamentalDomain H s μ :=
  hs.preimage_of_equiv (Measure.QuasiMeasurePreserving.id μ)
    (Subgroup.subgroupOfEquivOfLe h).bijective (fun _ _ => rfl)
end QEC.Coding.TannerLiftedProduct
