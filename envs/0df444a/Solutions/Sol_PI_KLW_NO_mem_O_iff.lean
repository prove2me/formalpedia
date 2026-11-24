-- Prove2me | solution 1 for PI.KLW.NO.mem_O_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:18.136061+00:00
-- url     : https://prove2.me/submissions/01285527-7627-4dc4-a8e9-a6a438c30d98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA

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
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] {x : K} :
    x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y
  · intro h; exact ⟨⟨x, h⟩, rfl⟩
end PI.KLW.NO
