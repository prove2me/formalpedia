-- Prove2me | solution 1 for PI.VolStabW.fFSplit_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:39:31.972861+00:00
-- url     : https://prove2.me/submissions/993505f9-f0de-483c-9555-fee172548591

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_fFSplit_nat

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
namespace PI.VolStabW
theorem _root_.solution : FFSplit := by
  intro k _ _ M a ha J hJ hJd T hT hTd
  rw [FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd]
  have hq : 0 < Nat.card k := Nat.card_pos
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl
end PI.VolStabW
