-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_linear_924a42cd360c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:22.669625+00:00
-- url     : https://prove2.me/submissions/7055d218-e313-4e8c-9f4e-a0391785347a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahlerMul_d866b4823dac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sphereMeanLinear_a6c63502716d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {d : ℕ}
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (c : Fin d → ℂ) (hc : ∃ j, c j ≠ 0) :
    mahler (HermNorm.std d) 1 (∑ j, C (c j) * X ((0 : Fin 1), j)) =
      Real.log √(∑ j, ‖c j‖ ^ 2) - (harmonic (d - 1) : ℝ) / 2 := by
  obtain ⟨j0, hj0⟩ := hc
  set S := ∑ j, ‖c j‖ ^ 2 with hS
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity : 0 < ‖c j0‖ ^ 2)
    (Finset.single_le_sum (f := fun j ↦ ‖c j‖ ^ 2) (fun j _ ↦ by positivity) (Finset.mem_univ j0))
  set ν := √S with hνdef
  have hν : 0 < ν := Real.sqrt_pos.mpr hSpos
  have hν2 : ν ^ 2 = S := Real.sq_sqrt hSpos.le
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  set p : Fin d → ℂ := fun j ↦ star (c j) / (ν : ℂ) with hpdef
  have hsplit : (∑ j, C (c j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) ℂ) =
      C (ν : ℂ) * ∑ j, C (star (p j)) * X ((0 : Fin 1), j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, ← C_mul]
    congr 2
    simp only [p, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
  have hp : ∑ j, ‖p j‖ ^ 2 = 1 := by
    simp only [p, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν, div_pow,
      ← Finset.sum_div, hν2]
    exact div_self hSpos.ne'
  have hL : (∑ j, C (star (p j)) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg (eval fun ij : Fin 1 × Fin d ↦ p ij.2) h0
    simp only [map_sum, map_mul, eval_C, eval_X, map_zero, Complex.star_def, Complex.conj_mul'] at h1
    have h2 : ((∑ j, ‖p j‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h1
    rw [hp] at h2
    norm_num at h2
  rw [hsplit, mahlerMul d 1 _ _ _ (C_ne_zero.mpr hνC) hL, mahler_C, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hν]
  have hlin := sphereMeanLinear d p hp
  have hfun : (fun u : Fin 1 × Fin d → ℂ ↦
      Real.log ‖eval u (∑ j, C (star (p j)) * X ((0 : Fin 1), j))‖) =
      fun z ↦ Real.log ‖∑ j, z (0, j) * star (p j)‖ := by
    funext u
    simp only [map_sum, map_mul, eval_C, eval_X, mul_comm]
  unfold mahler
  rw [hfun, hlin]
  ring
end GroundTheory.Heights₂.Heights.FibreMahlerForms
