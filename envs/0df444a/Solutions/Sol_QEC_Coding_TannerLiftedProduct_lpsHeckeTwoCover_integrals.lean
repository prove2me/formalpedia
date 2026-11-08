-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeTwoCover_integrals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:16:37.52467+00:00
-- url     : https://prove2.me/submissions/2039ec6f-4ac1-4efc-8d6b-e05597f0da78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeLeftImageCover_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightCover_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeInversePetersson_effective_invariant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    (∫τ in lpsHeckeUpperGL ℝ p none •
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s),
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ) =
      ∫τ in (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s),
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ :=
  (lpsHeckeLeftImageCover_fundamental N p hNp hs).setIntegral_eq
    (lpsHeckeRightCover_fundamental N p hNp hs)
    (lpsHeckeInversePetersson_effective_invariant N p f g)
end QEC.Coding.TannerLiftedProduct
