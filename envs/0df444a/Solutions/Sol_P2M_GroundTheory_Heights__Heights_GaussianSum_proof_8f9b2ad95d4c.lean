-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussianSum_proof_8f9b2ad95d4c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:00.95206+00:00
-- url     : https://prove2.me/submissions/1333e389-7e9d-466b-833d-b0b499256a9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussTop

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
open Matrix Real
namespace GroundTheory.Heights₂.Heights
namespace GaussianSum
theorem _root_.solution (hPD : GaussPoissonDual.Statement) (hSS : GaussShellSum.Statement)
    (hC : GaussConstant.Statement) : GaussianSum.Statement := by
  refine ⟨72 * Real.exp 4, by positivity, ?_⟩
  intro g Y ρ hY hρ hmin u
  obtain ⟨hsum, Λ, hΛ, hle⟩ := hPD g Y ρ hY hρ hmin u
  refine ⟨hsum, ?_⟩
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hq : ∀ k : Fin 0 → ℤ, qf Y (intVec k + u) = 0 := fun k => by simp [qf]
    simp only [hq, mul_zero, Real.exp_zero, tsum_const, Nat.card_unique, one_smul,
      Nat.cast_zero, zero_div, Real.rpow_zero, Matrix.det_isEmpty, Real.one_rpow, pow_zero,
      mul_one, le_refl]
  · have hdet : 0 < Y.det := hY.det_pos
    have hd : 0 ≤ Y.det ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hdet.le _
    have hS := (hSS g hg Λ ρ hρ hΛ).2
    have hc := hC g hg
    have hr : 0 ≤ (1 + 1 / ρ) ^ g := by positivity
    calc ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u))
        ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := hle
      _ ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) * (2 * gaussShellConst g * (1 + 1 / ρ) ^ g) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 ^ g * (2 * gaussShellConst g) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g := by ring
      _ ≤ (72 * Real.exp 4 * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) hr
end GaussianSum
end GroundTheory.Heights₂.Heights
