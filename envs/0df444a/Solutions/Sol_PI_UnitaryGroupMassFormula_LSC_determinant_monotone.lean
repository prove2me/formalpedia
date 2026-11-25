-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.determinant_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:37.447779+00:00
-- url     : https://prove2.me/submissions/ce54a4e6-3d3f-46e1-87d2-a8e45c0b1323

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_quad
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_sandwich
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_nsq_nonneg
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_posDefCongruentOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC
open DeterminantMonotonicity
namespace PI.UnitaryGroupMassFormula.LSC
theorem _root_.solution : DetMono := by
  intro n j C M κ hκ hM
  classical
  have hB : (Cᴴ * C).PosSemidef := posSemidef_conjTranspose_mul_self C
  have hA : ((M * C)ᴴ * (M * C)).PosSemidef := posSemidef_conjTranspose_mul_self (M * C)
  have hBre : 0 ≤ ((Cᴴ * C).det).re := by
    simpa using (Complex.le_def.mp hB.det_nonneg).1
  refine ⟨hBre, ?_⟩
  have hqA : ∀ z : Fin j → ℂ, star z ⬝ᵥ (((M * C)ᴴ * (M * C)) *ᵥ z) = ((nsq (M *ᵥ (C *ᵥ z)) : ℝ) : ℂ) := by
    intro z; rw [quad, mulVec_mulVec]
  by_cases h0 : (Cᴴ * C).det = 0
  · obtain ⟨z, hz, hBz⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : nsq (C *ᵥ z) = 0 := by
      have := quad C z
      rw [hBz, dotProduct_zero] at this
      exact_mod_cast this.symm
    have h2 : nsq (M *ᵥ (C *ᵥ z)) = 0 :=
      le_antisymm (by simpa [h1] using hM (C *ᵥ z)) (nsq_nonneg _)
    have h3 : ((M * C)ᴴ * (M * C)) *ᵥ z = 0 := by
      rw [← hA.dotProduct_mulVec_zero_iff, hqA, h2]; simp
    have h4 : ((M * C)ᴴ * (M * C)).det = 0 := exists_mulVec_eq_zero_iff.mp ⟨z, hz, h3⟩
    rw [h4, h0]; simp
  · have hPD : (Cᴴ * C).PosDef := hB.posDef_iff_det_ne_zero.mpr h0
    obtain ⟨y, hy, hyB⟩ := posDefCongruentOne j _ hPD
    have hN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).PosSemidef := hA.conjTranspose_mul_mul_same y
    have hev : ∀ i, hN.1.eigenvalues i ≤ κ := by
      intro i
      have hv1 : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ ⇑(hN.1.eigenvectorBasis i) = 1 := by
        rw [dotProduct_comm]
        simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
          hN.1.eigenvectorBasis.orthonormal.1 i]
        simp
      have hBv : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ
          ((yᴴ * (Cᴴ * C) * y) *ᵥ ⇑(hN.1.eigenvectorBasis i)) = 1 := by
        rw [hyB, one_mulVec, hv1]
      rw [sandwich, quad] at hBv
      have hn1 : nsq (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i))) = 1 := by exact_mod_cast hBv
      rw [hN.1.eigenvalues_eq, sandwich, hqA]
      have := hM (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i)))
      rw [hn1, mul_one] at this
      simpa using this
    have hdetN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).det = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hN.1.det_eq_prod_eigenvalues]; push_cast; rfl
    have hP : ∏ i, hN.1.eigenvalues i ≤ κ ^ j := by
      calc ∏ i, hN.1.eigenvalues i ≤ ∏ _i : Fin j, κ :=
            Finset.prod_le_prod (fun i _ => hN.eigenvalues_nonneg i) (fun i _ => hev i)
        _ = κ ^ j := by simp
    have hd0 : y.det ≠ 0 := hy.ne_zero
    have hnd : 0 < Complex.normSq y.det := Complex.normSq_pos.mpr hd0
    have e1 : ((Complex.normSq y.det : ℝ) : ℂ) * ((M * C)ᴴ * (M * C)).det
        = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [← hdetN, det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
      simp only [Complex.star_def]; ring
    have e2 : ((Complex.normSq y.det : ℝ) : ℂ) * (Cᴴ * C).det = 1 := by
      have := congrArg Matrix.det hyB
      rw [det_mul, det_mul, det_conjTranspose, det_one] at this
      rw [Complex.normSq_eq_conj_mul_self, ← this]
      simp only [Complex.star_def]; ring
    have r1 := congrArg Complex.re e1
    have r2 := congrArg Complex.re e2
    rw [Complex.re_ofReal_mul, Complex.ofReal_re] at r1
    rw [Complex.re_ofReal_mul, Complex.one_re] at r2
    refine le_of_mul_le_mul_left ?_ hnd
    calc Complex.normSq y.det * (((M * C)ᴴ * (M * C)).det).re = ∏ i, hN.1.eigenvalues i := r1
      _ ≤ κ ^ j := hP
      _ = κ ^ j * (Complex.normSq y.det * ((Cᴴ * C).det).re) := by rw [r2, mul_one]
      _ = Complex.normSq y.det * (κ ^ j * ((Cᴴ * C).det).re) := by ring
end PI.UnitaryGroupMassFormula.LSC
