-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeLeft_cover_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:11:40.656001+00:00
-- url     : https://prove2.me/submissions/e38d3d9a-ff0e-4652-9def-3ba0ae00bf2a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_sum_left
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionEffectiveRepresentative_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeLeft_density
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_integrable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∫τ in lpsHeckeUpperGL ℝ p none •
        (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N),
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  let F : ℍ→ℂ := petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
  let FA : ℍ→ℂ := fun τ => F (lpsHeckeUpperGL ℝ p none • τ)
  have hi (i : Option (Fin p)) : IntegrableOn FA
      ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N) volume := by
    apply ((measurePreserving_smul (lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ volume).integrableOn_image
      (measurableEmbedding_const_smul (lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹)).mpr
    have h := lpsWeightTwoSlashPetersson_integrable N f g (lpsHeckeUpperGL ℝ p i)
      (by rw [lpsHeckeUpperGL_det];exact_mod_cast (Fact.out:p.Prime).pos)
    apply h.congr
    exact Eventually.of_forall (lpsHeckeLeft_density N p hNp f g i)
  rw [lpsCuspHeckePairing_sum_left]
  have he := lpsIndexedRelativeDomain_integral _ (lpsGamma0PeterssonDomain N)
    (lpsGamma0PeterssonDomain_fundamental N)
    (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm
    (lpsHeckeIntersectionEffectiveRepresentative N p hNp)
    (lpsHeckeIntersectionEffectiveRepresentative_mk N p hNp) FA hi
  calc
    _ = ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        FA ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • τ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Eventually.of_forall (lpsHeckeLeft_density N p hNp f g i)
    _ = ∫τ in ⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ •
        lpsGamma0PeterssonDomain N,FA τ := he.symm
    _ = _ := ((measurePreserving_smul (lpsHeckeUpperGL ℝ p none) volume).setIntegral_image_emb
      (measurableEmbedding_const_smul (lpsHeckeUpperGL ℝ p none)) F _).symm
end QEC.Coding.TannerLiftedProduct
