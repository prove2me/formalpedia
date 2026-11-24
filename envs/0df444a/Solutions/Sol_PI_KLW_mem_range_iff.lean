-- Prove2me | solution 1 for PI.KLW.mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:09.508802+00:00
-- url     : https://prove2.me/submissions/03b3dc60-510f-4682-bf10-99ee9ec811a0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral

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
variable {K : Type} [Field K] [NumberField K]
namespace PI.KLW
theorem _root_.solution {x : K} : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩
end PI.KLW
