-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.linInd_of_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:08.433945+00:00
-- url     : https://prove2.me/submissions/faa3f2e8-a052-4e4e-9d40-d460b536d17a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_linInd_cols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  refine (linInd_cols_iff P).mpr fun v hv ↦ ?_
  have : W *ᵥ (P *ᵥ v) = (W * P) *ᵥ v := Matrix.mulVec_mulVec _ _ _
  rw [h, Matrix.one_mulVec, hv, Matrix.mulVec_zero] at this
  exact this.symm
end PI.VolStabW.FiniteFieldSplitting
