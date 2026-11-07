-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:23.683006+00:00
-- url     : https://prove2.me/submissions/d6cd1470-fa04-45cd-85e7-fcc7ea909748

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_components

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
omit [Countable G]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) (F : α → E)
    (hF : ∀i,IntegrableOn F ((r i)⁻¹ • s) μ) :
    (∫x in ⋃i,(r i)⁻¹ • s,F x ∂μ)=∑i,∫x in s,F ((r i)⁻¹ • x) ∂μ := by
  rw [integral_iUnion_ae (fun i => hs.nullMeasurableSet_smul (r i)⁻¹)
    (lpsIndexedRelativeDomain_components H s hs e r hr) (integrableOn_finite_iUnion.mpr hF),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (MeasureTheory.measurePreserving_smul (r i)⁻¹ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul (r i)⁻¹) F s
end QEC.Coding.TannerLiftedProduct
