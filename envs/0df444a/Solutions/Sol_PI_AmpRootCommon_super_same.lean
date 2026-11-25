-- Prove2me | solution 1 for PI.AmpRootCommon.super_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:54.077799+00:00
-- url     : https://prove2.me/submissions/6570b495-7284-41c8-81b7-81f696c479ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_SuperdiagPairingAdjacent
import Theorems.Thm_PI_AmpRootCommon_inv_superdiag
import Theorems.Thm_PI_AmpRootCommon_relA

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
    (hζ : ∀ i, ζ i ≠ 0) (hu : u.BlockTriangular id) (hud : ∀ i, u i i = 1) (hrel : uᴴ * Z * u' = Z)
    (i i1 : Fin n) (h1 : (σ i1).val + 1 = (σ i).val) (h2 : ζ (σ i1) = - ζ (σ i)) :
    u' i i1 = star (u (σ i1) (σ i)) := by
  have h := relA hσ hZ hu hud hrel (σ i) i1
  rw [hσ, inv_superdiag hu hud (σ i1) (σ i) h1, h2, star_neg] at h
  apply mul_left_cancel₀ (hζ (σ i))
  linear_combination h
end PI.AmpRootCommon
