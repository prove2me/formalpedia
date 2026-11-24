-- Prove2me | solution 1 for PI.KLW.conjK_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:06.865893+00:00
-- url     : https://prove2.me/submissions/1541c002-181e-4072-89cb-199da450f487

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType

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
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') (k : K) :
    algebraMap K E (conjK cj h k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (h k)).symm
end PI.KLW
