-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIndexedRelativeDomain_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:22.500873+00:00
-- url     : https://prove2.me/submissions/88df1e53-81b5-406c-af39-5ed08bb01b5d

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsRelativeDomain_fundamental

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
omit [Fintype I]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup G) (s : Set α)
    (hs : IsFundamentalDomain G s μ) (e : I ≃ G ⧸ H) (r : I → G)
    (hr : ∀i,QuotientGroup.mk (r i)=e i) :
    IsFundamentalDomain H (⋃i,(r i)⁻¹ • s) μ := by
  have heq : (⋃i,(r i)⁻¹ • s)=lpsRelativeDomain H s (fun c => r (e.symm c)) := by
    ext x
    simp only [lpsRelativeDomain,Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e i,by simpa using hi⟩
    · rintro ⟨c,hc⟩
      exact ⟨e.symm c,hc⟩
  rw [heq]
  exact lpsRelativeDomain_fundamental H s _ (by intro c;simpa using hr (e.symm c)) hs
end QEC.Coding.TannerLiftedProduct
