-- Prove2me | solution 1 for SumProduct.conePolarCorrection_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:05.89041+00:00
-- url     : https://prove2.me/submissions/3eb8eefa-98cf-421a-b273-407faed75c50

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (s : ℝ) :
    conePolarCorrection K 𝔞 (s : ℂ)
      = ((- (surfaceVolume K).re / s
          + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1) : ℝ) : ℂ) := by
  have hVre : (surfaceVolume K) = ((surfaceVolume K).re : ℂ) := by
    rw [surfaceVolume]; simp
  have hcov : (Theta.covolume K 𝔞 : ℂ)⁻¹ = ((1 / Theta.covolume K 𝔞 : ℝ) : ℂ) := by
    push_cast; ring
  rw [conePolarCorrection, hcov]
  conv_lhs => rw [hVre]
  push_cast
  ring
end SumProduct
