-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCosetSectionDomain_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:46.167344+00:00
-- url     : https://prove2.me/submissions/1880d14a-6546-4821-83ee-2114efe8ae67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_components
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveMeasurableEmbedding


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    [H.FiniteIndex] (r : lpsEffectiveModularGroup ⧸ H → lpsEffectiveModularGroup)
    (hr : ∀c, QuotientGroup.mk (r c) = c) (F : ℍ → ℂ)
    (hF : ∀c, IntegrableOn F ((r c)⁻¹ • ModularGroup.fd) volume) :
    (∫τ in lpsCosetSectionDomain H r, F τ) =
      ∑' c, ∫τ in ModularGroup.fd, F ((r c)⁻¹ • τ) := by
  let : Fintype (lpsEffectiveModularGroup ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  unfold lpsCosetSectionDomain
  rw [integral_iUnion_ae
    (fun c => lpsEffectiveFundamentalDomain.nullMeasurableSet_smul (r c)⁻¹)
    (lpsCosetSectionDomain_components H r hr) (integrableOn_finite_iUnion.mpr hF)]
  apply tsum_congr
  intro c
  exact (lpsEffectiveMeasurePreserving (r c)⁻¹).setIntegral_image_emb
    (lpsEffectiveMeasurableEmbedding (r c)⁻¹) F ModularGroup.fd
end QEC.Coding.TannerLiftedProduct
