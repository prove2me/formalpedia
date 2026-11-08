-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeInversePetersson_effective_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:30.108484+00:00
-- url     : https://prove2.me/submissions/38323e2b-38d1-4acc-ade0-06b60ebab121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeInversePetersson_gamma_invariant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveHeckeConjugateIntersection N p) (τ : ℍ) :
    petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) (h • τ) =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  obtain ⟨δ,hδ,hδh⟩ := Subgroup.mem_map.mp h.property
  change petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
    (((h:lpsEffectiveModularGroup):Equiv.Perm ℍ) τ)=_
  rw [←hδh]
  exact lpsHeckeInversePetersson_gamma_invariant N p f g δ hδ τ
end QEC.Coding.TannerLiftedProduct
