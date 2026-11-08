-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeLeft_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:50.919028+00:00
-- url     : https://prove2.me/submissions/bfcce470-e1b9-424a-87c7-853d0cfd9d53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionRepresentative_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_transfer


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) (τ : ℍ) :
    petersson 2 (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) g τ =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
        (lpsHeckeUpperGL ℝ p none •
          ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • τ)) := by
  let γ : SL(2,ℤ) := (lpsHeckeIntersectionRepresentative N p hNp i : SL(2,ℤ))⁻¹
  have hγ : γ∈CongruenceSubgroup.Gamma0 N := (CongruenceSubgroup.Gamma0 N).inv_mem
    (lpsHeckeIntersectionRepresentative N p hNp i).property
  obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersectionRepresentative_factor N p hNp i
  have hf : ((f:ℍ→ℂ) ∣[(2:ℤ)]
      (lpsHeckeUpperGL ℝ p none*Matrix.SpecialLinearGroup.mapGL ℝ γ)) =
        ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) := by
    rw [he,SlashAction.slash_mul]
    change (((f:ℍ→ℂ) ∣[(2:ℤ)] δ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i)=_
    rw [lpsWeightTwoCusp_slash_gamma0 N f δ hδ]
  have hp := petersson_slash_SL 2 ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p none) (g:ℍ→ℂ) γ τ
  rw [lpsWeightTwoCusp_slash_gamma0 N g γ hγ] at hp
  change petersson 2 (((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p none) ∣[(2:ℤ)]
    Matrix.SpecialLinearGroup.mapGL ℝ γ) g τ = _ at hp
  rw [←SlashAction.slash_mul,hf] at hp
  rw [hp,lpsWeightTwoPetersson_transfer]
  · rfl
  · rw [lpsHeckeUpperGL_det]
    exact_mod_cast (Fact.out:p.Prime).pos
end QEC.Coding.TannerLiftedProduct
