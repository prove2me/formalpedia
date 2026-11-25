-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:31.03645+00:00
-- url     : https://prove2.me/submissions/d1343904-2956-4752-a8a0-0b1dd82f35e4

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_polar_mul
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_radial
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_norm_sphMonomL
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_sphMonomMu
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_finrank_sphMonomE
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_sqN_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution [NeZero N] {k : ℕ} (f : (Fin N → ℂ) → ℂ)
    (hf : ∀ (r : ℝ) (z : Fin N → ℂ), f (r • z) = (r : ℂ) ^ k * f z) :
    (∫ z, f z * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + 0 : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) =
      (∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ)) *
        ((Real.Gamma ((((2 * N - 1 + k : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  have hzs : ∀ z : Fin N → ℂ, z = Real.sqrt (sqN z) • ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    by_cases hs : Real.sqrt (sqN z) = 0
    · have h0 : sqN z = 0 := by
        have := Real.sqrt_eq_zero'.1 hs
        linarith [sphMonom_sqN_nonneg z]
      have hz : z = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖z j‖)).1 h0 i (Finset.mem_univ i)
        simpa using this
      rw [hs, zero_smul]
      exact hz
    · rw [smul_inv_smul₀ hs]
  have hhom : ∀ z, f z = ((Real.sqrt (sqN z) : ℝ) : ℂ) ^ k * f ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    conv_lhs => rw [hzs z]
    exact hf _ _
  have hexp : ∀ z : Fin N → ℂ, Real.exp (-sqN z) = Real.exp (-(Real.sqrt (sqN z)) ^ 2) := by
    intro z
    rw [Real.sq_sqrt (sphMonom_sqN_nonneg z)]
  let G : EuclideanSpace ℂ (Fin N) → ℂ := fun y => f ((sphMonomL N).symm y)
  have hG : ∀ z, G (‖sphMonomL N z‖⁻¹ • sphMonomL N z) = f ((Real.sqrt (sqN z))⁻¹ • z) := by
    intro z
    simp only [G, map_smul, ContinuousLinearEquiv.symm_apply_apply, norm_sphMonomL]
  have hrad : ∀ j, ∫ r : Ioi (0 : ℝ), r.1 ^ j * Real.exp (-(r.1 ^ 2))
      ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) - 1)) =
        Real.Gamma ((((2 * N - 1 + j : ℕ) : ℝ) + 1) / 2) / 2 := by
    intro j
    rw [finrank_sphMonomE]
    exact sphMonom_radial (2 * N - 1) j
  have hpol : ∀ j, ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ j * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) =
      (∫ u : sphere (0 : EuclideanSpace ℂ (Fin N)) 1, G u ∂(sphMonomMu N).toSphere) *
        ((Real.Gamma ((((2 * N - 1 + j : ℕ) : ℝ) + 1) / 2) / 2 : ℝ) : ℂ) := by
    intro j
    refine (sphMonom_polar_mul (sphMonomMu N) G (fun r => r ^ j * Real.exp (-(r ^ 2)))).trans ?_
    congr 1
    exact_mod_cast hrad j
  have hL1 : ∫ z, f z * (Real.exp (-sqN z) : ℂ) =
      ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ k * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) := by
    rw [integral_sphMonomMu]
    congr 1
    funext z
    rw [hG z, norm_sphMonomL, hhom z, hexp z]
    push_cast
    ring
  have hL2 : ∫ z, f ((Real.sqrt (sqN z))⁻¹ • z) * (Real.exp (-sqN z) : ℂ) =
      ∫ x, G (‖x‖⁻¹ • x) * (((‖x‖ ^ 0 * Real.exp (-(‖x‖ ^ 2)) : ℝ)) : ℂ) ∂(sphMonomMu N) := by
    rw [integral_sphMonomMu]
    congr 1
    funext z
    rw [hG z, norm_sphMonomL, hexp z]
    push_cast
    ring
  rw [hL1, hL2, hpol k, hpol 0]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
