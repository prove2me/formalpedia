-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRight_cover_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:17:21.542504+00:00
-- url     : https://prove2.me/submissions/47dd6188-4bd1-49de-8cb5-9b7c452d9c5c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_sum_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateEffectiveRepresentative_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRight_density
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIndexedRelativeDomain_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_right_integrable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) =
      ∫τ in ⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N,
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  let F : ℍ→ℂ := petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
  have hi (i : Option (Fin p)) : IntegrableOn F
      ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N) volume := by
    apply ((measurePreserving_smul (lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ volume).integrableOn_image
      (measurableEmbedding_const_smul (lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹)).mpr
    have h := lpsWeightTwoSlashPetersson_right_integrable N f g (lpsHeckeUpperGL ℝ p i)
      (by rw [lpsHeckeUpperGL_det];exact_mod_cast (Fact.out:p.Prime).pos)
    apply h.congr
    exact Eventually.of_forall (lpsHeckeRight_density N p hNp f g i)
  rw [lpsCuspHeckePairing_sum_right]
  have he := lpsIndexedRelativeDomain_integral _ (lpsGamma0PeterssonDomain N)
    (lpsGamma0PeterssonDomain_fundamental N)
    (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm
    (lpsHeckeConjugateEffectiveRepresentative N p hNp)
    (lpsHeckeConjugateEffectiveRepresentative_mk N p hNp) F hi
  calc
    _ = ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        F ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • τ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Eventually.of_forall (lpsHeckeRight_density N p hNp f g i)
    _ = _ := he.symm
end QEC.Coding.TannerLiftedProduct
