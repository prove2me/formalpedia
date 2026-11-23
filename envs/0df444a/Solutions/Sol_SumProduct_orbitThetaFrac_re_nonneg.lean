-- Prove2me | solution 1 for SumProduct.orbitThetaFrac_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:13.952942+00:00
-- url     : https://prove2.me/submissions/1dee396c-f0b7-4946-963b-b0e39151c191

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
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) :
    (orbitThetaFrac K I r).im = 0 ∧ 0 ≤ (orbitThetaFrac K I r).re := by
  have h : orbitThetaFrac K I r
      = ((∫ σ in normEqOneSurface K,
          (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
            Theta.mixedGaussian K (radialMap K r σ * mixedEmbedding K (a : K)))
          ∂(surfaceMeasure K)) : ℝ) := by
    rw [orbitThetaFrac, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ _ => ?_)
    rw [Theta.mixedThetaKernel, Complex.ofReal_tsum]
  rw [h]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg (fun σ => tsum_nonneg (fun a => mixedGaussian_nonneg _))
end SumProduct
