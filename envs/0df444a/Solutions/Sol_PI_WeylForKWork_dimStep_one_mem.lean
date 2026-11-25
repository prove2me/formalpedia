-- Prove2me | solution 1 for PI.WeylForKWork.dimStep_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:25.047631+00:00
-- url     : https://prove2.me/submissions/3a5c08c3-788d-4c01-945a-86e33bccbef2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix DimensionInduction
namespace PI.WeylForKWork
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
end PI.WeylForKWork
