-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:04:45.212085+00:00
-- url     : https://prove2.me/submissions/3d042202-b0f7-42d8-ac00-7369b33c08a0

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
    (r : G ⧸ H → G) (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) :
    ∀ᵐ τ ∂μ,∃h : H,h • τ ∈ lpsRelativeDomain H s r := by
  filter_upwards [hs.ae_covers] with τ hτ
  obtain ⟨g,hg⟩ := hτ
  let g' : G := g
  let c : G ⧸ H := QuotientGroup.mk g'
  have hc : QuotientGroup.mk (r c) = QuotientGroup.mk g' := hr c
  have hk : (r c)⁻¹*g' ∈ H := QuotientGroup.eq.mp hc
  let h : H := ⟨(r c)⁻¹*g',hk⟩
  refine ⟨h,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
  rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
  change (r c) • (((r c)⁻¹*g') • τ) ∈ s
  rw [←mul_smul,mul_inv_cancel_left]
  exact hg
end QEC.Coding.TannerLiftedProduct
