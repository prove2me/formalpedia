-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_vecCons_const_of_ne_zero_1d7340a79bae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:29.941474+00:00
-- url     : https://prove2.me/submissions/5b03eb91-aef1-49a4-bf1f-701b70b8dc65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {d : ℕ} (y x : K → ℤ) (k : Fin (d + 1)) (hk : k ≠ 0) :
    Matrix.vecCons y (fun _ : Fin d => x) k = x := by
  obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr hk
  simp
end GroundTheory.Heights₂.Heights.HilbertSamuel
