-- Prove2me | solution 1 for SumProduct.orbitTheta_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:04.685992+00:00
-- url     : https://prove2.me/submissions/3fe799b7-0c3a-4c90-947b-11a440ce3e76

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mixedGaussian_nonneg


set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
variable {K}
namespace SumProduct
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (r : ℝ) :
    (orbitTheta K 𝔞 r).im = 0 ∧ 0 ≤ (orbitTheta K 𝔞 r).re := by
  have h : orbitTheta K 𝔞 r
      = ((∫ σ in normEqOneSurface K,
          (∑' a : {a : 𝓞 K // a ∈ 𝔞 ∧ a ≠ 0},
            Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K ((a : 𝓞 K) : K)))
          ∂(surfaceMeasure K)) : ℝ) := by
    rw [orbitTheta, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ _ => ?_)
    rw [Theta.idealThetaKernel, Complex.ofReal_tsum]
  rw [h]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg (fun σ => tsum_nonneg (fun a => mixedGaussian_nonneg _))
end SumProduct
