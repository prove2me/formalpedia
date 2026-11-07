-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:17:41.166193+00:00
-- url     : https://prove2.me/submissions/efe00c79-a5e0-4e6a-b048-cc770953c0d4

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
omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup G) (s : Set α)
    (r : G ⧸ H → G)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    Pairwise (fun c d => AEDisjoint μ ((r c)⁻¹ • s)
      ((r d)⁻¹ • s)) := by
  intro c d hcd
  apply hs.aedisjoint
  intro he
  apply hcd
  have he' : r c = r d := inv_injective he
  exact (hr c).symm.trans ((congrArg (QuotientGroup.mk : G →
    G ⧸ H) he').trans (hr d))
end QEC.Coding.TannerLiftedProduct
