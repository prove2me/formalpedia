-- Prove2me | solution 1 for PI.VolStabSW.FiniteFieldSplitting.linInd_of_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:39.280376+00:00
-- url     : https://prove2.me/submissions/1c74b665-b348-4fc2-b876-da361b98c9b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_linInd_cols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabSW.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]
end PI.VolStabSW.FiniteFieldSplitting
