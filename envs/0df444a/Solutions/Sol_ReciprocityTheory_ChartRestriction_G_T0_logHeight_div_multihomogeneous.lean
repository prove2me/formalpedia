-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.logHeight_div_multihomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:21:57.909916+00:00
-- url     : https://prove2.me/submissions/050ce92d-761a-4f86-9153-5e5da6b26853

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightDivMultihomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLogIntegrable
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_blockSphere_eval_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_log_support_finite
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_pos_of_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_map_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {B n : ℕ} {P Q R : MvPolynomial (Fin B × Fin n) K}
    (eQ eR : Fin B → ℕ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hQm : IsMultiHomogeneous eQ Q)
    (hRm : IsMultiHomogeneous eR R) (hPQ : P * Q = R) :
    h0 P = h0 R - h0 Q := by
  have hR : R ≠ 0 := hPQ ▸ mul_ne_zero hP hQ
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w P) =
      (∑ᶠ w : FinitePlace K, Real.log (gaussAbs w R)) - ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w Q) := by
    rw [← finsum_sub_distrib (gauss_abs_log_support_finite R hR) (gauss_abs_log_support_finite Q hQ)]
    refine finsum_congr fun w => ?_
    rw [← hPQ, gauss_abs_mul w P Q hP hQ,
      Real.log_mul (gauss_abs_pos_of_ne_zero w P hP).ne' (gauss_abs_pos_of_ne_zero w Q hQ).ne']
    ring
  have harch : ∀ σ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map σ P) =
      blockSphereMean B n (MvPolynomial.map σ R) - blockSphereMean B n (MvPolynomial.map σ Q) := by
    intro σ
    have hs : ∀ F : MvPolynomial (Fin B × Fin n) K, F ≠ 0 → MvPolynomial.map σ F ≠ 0 := by
      intro F hF h'
      exact hF (MvPolynomial.map_injective σ σ.injective (by rw [h', map_zero]))
    have IR := sphereLogIntegrable B n eR _ (hs R hR) (isMultiHomogeneous_map_ring eR R hRm σ)
    have IQ := sphereLogIntegrable B n eQ _ (hs Q hQ) (isMultiHomogeneous_map_ring eQ Q hQm σ)
    have aR := ae_blockSphere_eval_ne_zero B n eR _ (hs R hR) (isMultiHomogeneous_map_ring eR R hRm σ)
    have aQ := ae_blockSphere_eval_ne_zero B n eQ _ (hs Q hQ) (isMultiHomogeneous_map_ring eQ Q hQm σ)
    unfold blockSphereMean
    rw [← integral_sub IR IQ]
    refine integral_congr_ae ?_
    filter_upwards [aR, aQ] with z hzR hzQ
    have hRe : MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ R) =
        MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ P) *
          MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ Q) := by
      rw [← hPQ, map_mul, map_mul]
    have hzP : MvPolynomial.eval (blockPoint z) (MvPolynomial.map σ P) ≠ 0 := by
      intro h0; apply hzR; rw [hRe, h0, zero_mul]
    rw [hRe, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hzP) (norm_ne_zero_iff.2 hzQ)]
    ring
  unfold h0
  rw [hfin, Finset.sum_congr rfl fun σ _ => harch σ, Finset.sum_sub_distrib]
  ring
end ReciprocityTheory.ChartRestriction.G.T0
