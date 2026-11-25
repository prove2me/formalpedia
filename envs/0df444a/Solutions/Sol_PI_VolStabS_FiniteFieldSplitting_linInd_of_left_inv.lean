-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldSplitting.linInd_of_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:41.042427+00:00
-- url     : https://prove2.me/submissions/9262038b-a731-427c-9cf1-e96a9951558d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabS_FiniteFieldSplitting_linInd_cols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabS.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]
end PI.VolStabS.FiniteFieldSplitting
