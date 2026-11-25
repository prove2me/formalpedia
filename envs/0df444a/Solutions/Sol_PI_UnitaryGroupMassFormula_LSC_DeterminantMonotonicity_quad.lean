-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:47.113351+00:00
-- url     : https://prove2.me/submissions/4359c443-9138-4b2b-8c3d-0e72ebad6045

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_DeterminantMonotonicity_star_dot_self

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
theorem _root_.solution {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (z : Fin j → ℂ) :
    star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = ((nsq (C *ᵥ z) : ℝ) : ℂ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self]
end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
