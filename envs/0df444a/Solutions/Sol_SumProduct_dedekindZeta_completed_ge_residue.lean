-- Prove2me | solution 1 for SumProduct.dedekindZeta_completed_ge_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:17:05.037839+00:00
-- url     : https://prove2.me/submissions/ce187733-9cd9-448d-a665-f409dbefb8bb

import Definitions.Def_SumProduct_PartialZetaMellin
import Definitions.Def_SumProduct_MultiplicativeCount
import Definitions.Def_SumProduct_EulerBound
import Definitions.Def_SumProduct_RegulatorBound
import Theorems.Thm_DedekindZeta_ConeRadialReduction_mem_normEqOneSurface
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_completedDedekindZeta_eq
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_partialCompletedZetaResidue_le
import Theorems.Thm_SumProduct_zInfty_ofReal
attribute [local simp] DedekindZeta.ConeRadialReduction.mem_normEqOneSurface
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply
attribute [local simp] SumProduct.idealCountArith_apply_ne
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection


section
open scoped NumberField
open Pointwise
namespace SumProduct
open NumberField NumberField.InfinitePlace NumberField.Units in
/-- Summing the per-class residue `2^rR/w` over all ideal classes gives the residue of the
completed Dedekind zeta in Mathlib's normalization. -/
private lemma completedResidue_eq_classNumber_mul_partialResidue (K : Type*) [Field K]
    [NumberField K] :
    NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
        / Real.pi ^ nrComplexPlaces K
      = (classNumber K : ℝ) * partialCompletedZetaResidue K := by
  have hΔ0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hsq : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := (Real.sqrt_pos.mpr hΔ0).ne'
  have hpi : Real.pi ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hw : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast torsionOrder_ne_zero K
  rw [NumberField.dedekindZeta_residue_def, partialCompletedZetaResidue]
  field_simp [hsq, hpi, hw]
  rw [pow_add, mul_pow]
  ring
end SumProduct
end

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField MeasureTheory NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K]
    (s : ℝ) (hs : 1 < s) :
    NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ nrComplexPlaces K
      ≤ s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K
          * (NumberField.dedekindZeta K (s : ℂ)).re := by
  have hsre : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  set ρ := partialCompletedZetaResidue K with hρdef
  have hpartial : ∀ C : ClassGroup (𝓞 K),
      ρ ≤ s * (s - 1)
          * (DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K C) (s : ℂ)).re := by
    intro C
    rw [hρdef]
    refine partialCompletedZetaResidue_le (K := K) (DedekindZeta.idealClassRep K C) ?_ hs
    exact mem_nonZeroDivisors_iff_ne_zero.mp (Function.surjInv ClassGroup.mk0_surjective C).2
  have hsumineq :
      (classNumber K : ℝ) * ρ
        ≤ s * (s - 1) * (DedekindZeta.completedDedekindZeta K (s : ℂ)).re := by
    have h := Finset.sum_le_sum
      (s := (Finset.univ : Finset (ClassGroup (𝓞 K)))) (fun C _ => hpartial C)
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h
    have hsumRe : (∑ C : ClassGroup (𝓞 K),
          (DedekindZeta.completedPartialZeta K (DedekindZeta.idealClassRep K C) (s : ℂ)).re)
        = (DedekindZeta.completedDedekindZeta K (s : ℂ)).re := by
      rw [DedekindZeta.completedDedekindZeta, Complex.re_sum]
    rw [hsumRe] at h
    rw [NumberField.classNumber]
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hcompRe : (DedekindZeta.completedDedekindZeta K (s : ℂ)).re
      = (|(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K)
        * (NumberField.dedekindZeta K (s : ℂ)).re := by
    rw [DedekindZeta.completedDedekindZeta_eq K hsre, zInfty_ofReal K s, Complex.re_ofReal_mul]
  calc NumberField.dedekindZeta_residue K * Real.sqrt |(NumberField.discr K : ℝ)|
          / Real.pi ^ nrComplexPlaces K
      = (classNumber K : ℝ) * ρ := by
          rw [hρdef, completedResidue_eq_classNumber_mul_partialResidue]
    _ ≤ s * (s - 1) * (DedekindZeta.completedDedekindZeta K (s : ℂ)).re := hsumineq
    _ = s * (s - 1) * |(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K
          * (NumberField.dedekindZeta K (s : ℂ)).re := by rw [hcompRe]; ring
end SumProduct
