-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.det_liftO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:07.750636+00:00
-- url     : https://prove2.me/submissions/5e0bc048-18e1-4662-9b09-1ec1d00b26b1

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_map_liftO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n F)
    (h : ∀ i j, N i j ∈ O) : ((liftO O N h).det : F) = N.det := by
  have := RingHom.map_det O.subtype (liftO O N h)
  rw [RingHom.mapMatrix_apply, map_liftO] at this
  exact this
end PI.DatumBlockEigen.Unit
