-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.hT_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:45:03.525524+00:00
-- url     : https://prove2.me/submissions/aa198e75-dace-4e5c-b5b3-f56958b03df6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gaussAbs_support_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_gaussAbs_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_torusMean_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_finsum_log_norm
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_pos_of_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sum_log_norm_embedding_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} [Fintype κ] (F : MvPolynomial κ K) (hF : F ≠ 0) (c : K) (hc : c ≠ 0) :
    hT (MvPolynomial.C c * F) = hT F := by
  unfold hT
  congr 1
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C c * F)) =
      ∑ᶠ w : FinitePlace K, Real.log (w c) +
        ∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w F) := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun w => ?_
      rw [gaussAbs_C_mul, Real.log_mul (FinitePlace.pos_iff.mpr hc).ne'
        (ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w F hF).ne']
    · refine (FinitePlace.hasFiniteMulSupport hc).subset ?_
      intro w hw h1
      apply hw
      simp only at h1 ⊢
      rw [h1, Real.log_one]
    · exact gaussAbs_support_finite F
  have harch : ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ (MvPolynomial.C c * F)) =
      ∑ σ : K →+* ℂ, Real.log ‖σ c‖ + ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ F) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, MvPolynomial.map_C]
    refine torusMean_C_mul _ ((map_ne_zero σ).mpr hc) _ ?_
    intro h0
    apply hF
    exact MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero])
  rw [hfin, harch, finsum_log_norm c hc, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq c hc]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
