-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_latticeForm_single_8e16640cd985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:32.652926+00:00
-- url     : https://prove2.me/submissions/f66dacc5-64e4-43bf-aac4-73731df913b8

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
theorem _root_.solution {m : ℕ} (j : Fin m) (a : K) :
    latticeForm (Pi.single j a : Fin m → K) = C a * X j := by
  rw [latticeForm, Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp)]
  simp
end GroundTheory.Heights₂.Heights
