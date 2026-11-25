-- Prove2me | solution 1 for PI.StabPairs.ConvAlg.rhoOf_mulVec_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:48.301895+00:00
-- url     : https://prove2.me/submissions/ebf54a1d-4ab9-48e3-af97-1e852df150f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg

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
open PI PI.StabPairs PI.StabPairs.ConvAlg
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
namespace PI.StabPairs.ConvAlg
theorem _root_.solution (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (v : n → ℂ) (hv : (Fᴴ * H) *ᵥ v = 0) : rhoOf H F W *ᵥ v = v := by
  rw [rhoOf, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hv]
  simp
end PI.StabPairs.ConvAlg
