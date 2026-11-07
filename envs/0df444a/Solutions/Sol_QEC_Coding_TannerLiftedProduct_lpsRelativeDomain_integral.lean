-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsRelativeDomain_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:04.976925+00:00
-- url     : https://prove2.me/submissions/cfda4380-2a4c-45bb-95c9-b38adfc06b22

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
    (hr : ∀c, QuotientGroup.mk (r c) = c) (hs : IsFundamentalDomain G s μ) (F : α → E)
    (hF : ∀c, IntegrableOn F ((r c)⁻¹ • s) μ) :
    (∫τ in lpsRelativeDomain H s r, F τ ∂μ) =
      ∑' c, ∫τ in s, F ((r c)⁻¹ • τ) ∂μ := by
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsRelativeDomain
  rw [integral_iUnion_ae
    (fun c => hs.nullMeasurableSet_smul (r c)⁻¹)
    (lpsRelativeDomain_components H s r hr hs) (integrableOn_finite_iUnion.mpr hF)]
  apply tsum_congr
  intro c
  exact (MeasureTheory.measurePreserving_smul (r c)⁻¹ μ).setIntegral_image_emb
    (measurableEmbedding_const_smul (r c)⁻¹) F s
end QEC.Coding.TannerLiftedProduct
