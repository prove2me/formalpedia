-- Prove2me | solution 1 for SumProduct.dedekindZeta_completed_residue_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:20:28.53022+00:00
-- url     : https://prove2.me/submissions/98d4aaa3-ddac-4b13-94a6-7c437cd4461b

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
import Theorems.Thm_SumProduct_dedekindZeta_completed_ge_residue
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply
attribute [local simp] SumProduct.idealCountArith_apply_ne
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (s : ℝ) (hs : 1 < s) :
    NumberField.dedekindZeta_residue K ≤
      s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
        * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
        * Real.Gamma (s / 2) ^ Module.finrank ℚ K
        * (NumberField.dedekindZeta K (s : ℂ)).re := by
  have hΔ0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hsqΔ : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| := Real.sqrt_pos.mpr hΔ0
  -- Specialize the general theorem to the totally real case.
  have hc : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero K
  have hr : nrRealPlaces K = Module.finrank ℚ K := (IsTotallyReal.finrank K).symm
  have h := dedekindZeta_completed_ge_residue K s hs
  rw [hc, hr] at h
  simp only [pow_zero, div_one, mul_one] at h
  -- `(π^{-s/2}Γ(s/2))^d = π^{-ds/2}·Γ(s/2)^d`.
  have hG : (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ Module.finrank ℚ K
      = Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
        * Real.Gamma (s / 2) ^ Module.finrank ℚ K := by
    rw [mul_pow]; congr 1
    rw [← Real.rpow_natCast (Real.pi ^ (-(s / 2))) (Module.finrank ℚ K),
      ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  -- `|Δ|^{(s-1)/2}·√|Δ| = |Δ|^{s/2}`.
  have hAA : |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2) * Real.sqrt |(NumberField.discr K : ℝ)|
      = |(NumberField.discr K : ℝ)| ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hΔ0]; congr 1; ring
  have hge' : NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
      ≤ (s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
          * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
          * Real.Gamma (s / 2) ^ Module.finrank ℚ K
          * (NumberField.dedekindZeta K (s : ℂ)).re)
        * Real.sqrt |(NumberField.discr K : ℝ)| := by
    calc NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
        ≤ s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
            * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ Module.finrank ℚ K
            * (NumberField.dedekindZeta K (s : ℂ)).re := h
      _ = (s * (s - 1) * |(NumberField.discr K : ℝ)| ^ ((s - 1) / 2)
            * Real.pi ^ (-(Module.finrank ℚ K : ℝ) * s / 2)
            * Real.Gamma (s / 2) ^ Module.finrank ℚ K
            * (NumberField.dedekindZeta K (s : ℂ)).re)
          * Real.sqrt |(NumberField.discr K : ℝ)| := by rw [hG, ← hAA]; ring
  exact le_of_mul_le_mul_right hge' hsqΔ
end SumProduct
