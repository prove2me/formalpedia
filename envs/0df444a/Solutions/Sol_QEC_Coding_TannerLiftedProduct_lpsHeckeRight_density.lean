-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRight_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:13:26.526778+00:00
-- url     : https://prove2.me/submissions/5e490986-b6d0-4217-8af4-2a47dbbd042b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeAdjointDensities
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateRepresentative_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeZero_slashInverse

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) (τ : ℍ) :
    petersson 2 f (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
        ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • τ) := by
  let γ : SL(2,ℤ) := (lpsHeckeConjugateRepresentative N p hNp i : SL(2,ℤ))⁻¹
  have hγ : γ∈CongruenceSubgroup.Gamma0 N := (CongruenceSubgroup.Gamma0 N).inv_mem
    (lpsHeckeConjugateRepresentative N p hNp i).property
  obtain ⟨δ,hδ,he⟩ := lpsHeckeConjugateRepresentative_factor N p hNp i
  have hg : ((g:ℍ→ℂ) ∣[(2:ℤ)]
      (lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)*Matrix.SpecialLinearGroup.mapGL ℝ γ)) =
        ((g:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) := by
    rw [he,SlashAction.slash_mul]
    change (((g:ℍ→ℂ) ∣[(2:ℤ)] δ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i)=_
    rw [lpsWeightTwoCusp_slash_gamma0 N g δ hδ]
  have hp := petersson_slash_SL 2 (f:ℍ→ℂ)
    ((g:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) γ τ
  rw [lpsWeightTwoCusp_slash_gamma0 N f γ hγ] at hp
  change petersson 2 f (((g:ℍ→ℂ) ∣[(2:ℤ)]
    lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) ∣[(2:ℤ)]
    Matrix.SpecialLinearGroup.mapGL ℝ γ) τ = _ at hp
  rw [←SlashAction.slash_mul,hg,lpsHeckeZero_slashInverse] at hp
  exact hp
end QEC.Coding.TannerLiftedProduct
