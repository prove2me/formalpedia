-- Prove2me | solution 1 for PI.AmpRootCommon.relB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:27.629436+00:00
-- url     : https://prove2.me/submissions/27a5ea87-1d7c-4aa6-9aad-db367b8dd80c

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
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z) (i j : Fin n) :
    star (u (σ j) i) * ζ (σ j) = ζ i * u'⁻¹ (σ i) j := by
  have hdet := isUnit_unitri hu' hud'
  have hZu : uᴴ * Z = Z * u'⁻¹ := by
    calc uᴴ * Z = uᴴ * Z * (u' * u'⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (uᴴ * Z * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Z * u'⁻¹ := by rw [hrel]
  have h := congrFun (congrFun hZu i) j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (σ j), Finset.sum_eq_single (σ i)] at h
  · rw [Z_at hZ, Z_at' hσ hZ, Matrix.conjTranspose_apply] at h
    exact h
  · intro b _ hb; rw [Z_row hZ i b hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; rw [Z_col hσ hZ a j ha, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.AmpRootCommon
