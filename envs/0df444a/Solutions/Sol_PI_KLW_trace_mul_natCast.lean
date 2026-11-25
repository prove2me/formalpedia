-- Prove2me | solution 1 for PI.KLW.trace_mul_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:59.292776+00:00
-- url     : https://prove2.me/submissions/887081da-8f87-4c42-8945-f6a899ecaa7e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (s : ℕ) (z y : E) :
    Algebra.trace K E (z * cj ((s : E) * y)) = (s : K) * Algebra.trace K E (z * cj y) := by
  have e : z * cj ((s : E) * y) = algebraMap K E (s : K) * (z * cj y) := by
    rw [map_mul cj, map_natCast cj, map_natCast]; ring
  rw [e, ← Algebra.smul_def, map_smul, smul_eq_mul]
end PI.KLW
