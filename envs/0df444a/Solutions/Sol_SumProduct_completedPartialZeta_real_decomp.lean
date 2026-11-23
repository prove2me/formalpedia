-- Prove2me | solution 1 for SumProduct.completedPartialZeta_real_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:07:05.304203+00:00
-- url     : https://prove2.me/submissions/6e3c089f-14bf-4590-9e0a-e9f34829f879

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin
import Theorems.Thm_SumProduct_partialZetaPrefactor_ofReal
import Theorems.Thm_SumProduct_conePolarCorrection_ofReal
import Theorems.Thm_DedekindZeta_ConeMellinBridge_completedPartialZeta_eq_conePolarCorrection_add_tail
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
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) {s : ℝ} (hs : 1 < s) :
    (DedekindZeta.completedPartialZeta K 𝔞 (s : ℂ)).re
      = ((1 / (Units.torsionOrder K : ℝ))
            * (Ideal.absNorm 𝔞 : ℝ) ^ s
            * (|(NumberField.discr K : ℝ)|) ^ (s / 2))
        * ((- (surfaceVolume K).re / s
            + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1))
          + (mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
              (surfaceVolume K) (surfaceVolume K)
              ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ)).re) := by
  have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  rw [completedPartialZeta_eq_conePolarCorrection_add_tail 𝔞 hne hsre,
    partialZetaPrefactor_ofReal 𝔞 s, conePolarCorrection_ofReal 𝔞 s]
  -- the bracket `(ofReal cone + tail)`: pull out the tail's real part
  set T := mellinTail (radialTheta K 𝔞) (radialThetaDual K 𝔞)
      (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 (s : ℂ) with hT
  set cp : ℝ := - (surfaceVolume K).re / s
      + (1 / Theta.covolume K 𝔞) * (surfaceVolume K).re / (s - 1) with hcp
  set pf : ℝ := (1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
      * (|(NumberField.discr K : ℝ)|) ^ (s / 2) with hpf
  -- `(ofReal pf * (ofReal cp + T)).re = pf * (cp + T.re)`
  rw [show ((pf : ℝ) : ℂ) * (((cp : ℝ) : ℂ) + T)
      = ((pf : ℂ) * (cp : ℂ)) + (pf : ℂ) * T by ring]
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  ring
end SumProduct
