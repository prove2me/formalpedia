-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_single_mul_a1dd377cfae2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:15.992169+00:00
-- url     : https://prove2.me/submissions/91b233be-3f47-4887-8166-742c6a543019

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints

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
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (σ : K →+* ℂ) (w : Fin m → ℂ) (j : Fin m) (a : K) :
    ∑ j', σ ((Pi.single j a : Fin m → K) j') * w j' = σ a * w j := by
  rw [Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp)]
  simp
end GroundTheory.Heights₂.Heights
