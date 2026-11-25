-- Prove2me | solution 1 for PI.AmpRootCommon.relA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:30.488992+00:00
-- url     : https://prove2.me/submissions/3b636b6f-14a5-4391-8656-af85c5d8400b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_isUnit_unitri
import Theorems.Thm_PI_AmpRootCommon_Z_row
import Theorems.Thm_PI_AmpRootCommon_Z_col
import Theorems.Thm_PI_AmpRootCommon_Z_at
import Theorems.Thm_P2M_PI_AmpRootCommon_Z_at__9514a3b6830f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.AmpRootCommon
variable {n : ℕ}
variable {Z u u' : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n} {ζ : Fin n → ℂ}
namespace PI.AmpRootCommon
theorem _root_.solution (hσ : ∀ i, σ (σ i) = i) (hZ : ∀ i j, Z i j = if j = σ i then ζ i else 0)
    (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    ζ i * u' (σ i) j = star (u⁻¹ (σ j) i) * ζ (σ j) := by
  have hdet := isUnit_unitri hu hud
  have hZu : Z * u' = (u⁻¹)ᴴ * Z := by
    calc Z * u' = ((u⁻¹)ᴴ * uᴴ) * Z * u' := by
          rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (u⁻¹)ᴴ * (uᴴ * Z * u') := by simp only [Matrix.mul_assoc]
      _ = (u⁻¹)ᴴ * Z := by rw [hrel]
  have h := congrFun (congrFun hZu i) j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ i), Finset.sum_eq_single (σ j)] at h
  · rw [Z_at hZ, Z_at' hσ hZ, Matrix.conjTranspose_apply] at h
    exact h
  · intro a _ ha; rw [Z_col hσ hZ a j ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [Z_row hZ i b hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.AmpRootCommon
