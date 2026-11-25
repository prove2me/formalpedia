-- Prove2me | solution 1 for PI.AmpRootCommon.super_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:12.201531+00:00
-- url     : https://prove2.me/submissions/11568995-4875-40aa-9007-36bb66c4251f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_inv_upper
import Theorems.Thm_PI_AmpRootCommon_relA
import Theorems.Thm_PI_AmpRootCommon_relB

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
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1)
    (hu' : u'.BlockTriangular id) (hud' : ∀ i, u' i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (hlt : (σ i).val < (σ i1).val) : u' i i1 = 0 ∧ u i i1 = 0 := by
  constructor
  · have h := relA hσ hZ hu hud hrel (σ i) i1
    rw [hσ, inv_upper hu hud (show id (σ i) < id (σ i1) from hlt), star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (hζ _)
  · have h := relB hσ hZ hu' hud' hrel i1 (σ i)
    rw [hσ, inv_upper hu' hud' (show id (σ i) < id (σ i1) from hlt), mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_right (hζ _)
    exact star_eq_zero.mp this
end PI.AmpRootCommon
