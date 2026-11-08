-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_sectionDomain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:05:48.278575+00:00
-- url     : https://prove2.me/submissions/1da5751d-bc7b-4523-bc8c-a4fd6927fb83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0CosetSection_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Petersson_translate_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_sectionSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveMeasurableEmbedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Domain_finiteIndex


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f g =
      ∫τ in lpsCosetSectionDomain (lpsEffectiveGamma0 N) (lpsGamma0CosetSection N), petersson 2 f g τ := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  let : Fintype (lpsEffectiveModularGroup ⧸ lpsEffectiveGamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  rw [lpsCosetSectionDomain_integral _ _ (lpsGamma0CosetSection_mk N) _
    (fun c => lpsGamma0Petersson_translate_integrable N f g _)]
  unfold lpsCuspPeterssonPairing
  simp_rw [lpsCuspPeterssonTrace_sectionSum,tsum_fintype]
  apply integral_finsetSum
  intro c _
  exact ((lpsEffectiveMeasurePreserving (lpsGamma0CosetSection N c)⁻¹).integrableOn_image
    (lpsEffectiveMeasurableEmbedding (lpsGamma0CosetSection N c)⁻¹)).mp
      (lpsGamma0Petersson_translate_integrable N f g _)
end QEC.Coding.TannerLiftedProduct
