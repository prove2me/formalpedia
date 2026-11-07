-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:10.705022+00:00
-- url     : https://prove2.me/submissions/7e7c437d-9c4a-41f0-8500-f57d97534a76

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
variable {G α I : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
  [Fintype I] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ] [Fintype I]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) :
    Pairwise (fun i j => AEDisjoint μ ((r i)⁻¹ • s) ((r j)⁻¹ • s)) := by
  intro i j hij
  apply hs.aedisjoint
  intro he
  apply hij
  apply e.injective
  rw [←hr i,←hr j,inv_injective he]
end QEC.Coding.TannerLiftedProduct
