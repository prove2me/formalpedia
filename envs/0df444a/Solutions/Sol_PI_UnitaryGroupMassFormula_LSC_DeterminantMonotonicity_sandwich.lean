-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:05.127255+00:00
-- url     : https://prove2.me/submissions/3f81ff46-6f95-42f4-8690-2fc7a3857d02

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono

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
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
namespace PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
theorem _root_.solution {j : ℕ} (y X : Matrix (Fin j) (Fin j) ℂ) (v : Fin j → ℂ) :
    star v ⬝ᵥ ((yᴴ * X * y) *ᵥ v) = star (y *ᵥ v) ⬝ᵥ (X *ᵥ (y *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
