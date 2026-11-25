-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_height_mul_multihomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:09.187328+00:00
-- url     : https://prove2.me/submissions/f9c2480b-3557-4451-a258-decaf1a3da39

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_log_support_finite
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_map_ring
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphere_mean_mul_multihomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_pos_of_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hInt : SphereLogIntegrableStatement) {K : Type*} [Field K] [NumberField K]
    (B n : ℕ) (a a' : Fin B → ℕ) (f g : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0)
    (haf : IsMultiHomogeneous a f) (hbg : IsMultiHomogeneous a' g) :
    h0 (f * g) = h0 f + h0 g := by
  unfold h0
  have hfin : ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w (f * g)) =
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) + ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w g) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite f hf) (gauss_abs_log_support_finite g hg)]
    refine finsum_congr fun w => ?_
    rw [gauss_abs_mul w f g hf hg, Real.log_mul (gauss_abs_pos_of_ne_zero w f hf).ne'
      (gauss_abs_pos_of_ne_zero w g hg).ne']
  have hinf : ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ (f * g)) =
      ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ f) +
        ∑ φ : K →+* ℂ, blockSphereMean B n (MvPolynomial.map φ g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have hinj := MvPolynomial.map_injective φ φ.injective (σ := Fin B × Fin n)
    rw [map_mul]
    exact sphere_mean_mul_multihomogeneous hInt B n a a' _ _
      (fun h => hf (hinj (by rw [h, map_zero])))
      (fun h => hg (hinj (by rw [h, map_zero])))
      (isMultiHomogeneous_map_ring a f haf φ) (isMultiHomogeneous_map_ring a' g hbg φ)
  rw [hfin, hinf]
  ring
end ReciprocityTheory.MultiplicativeHeights
