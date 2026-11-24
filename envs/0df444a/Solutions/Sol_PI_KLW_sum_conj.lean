-- Prove2me | solution 1 for PI.KLW.sum_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:21.557074+00:00
-- url     : https://prove2.me/submissions/7bd32261-32b1-4287-abb5-cd8798f2239d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Theorems.Thm_PI_KLW_conjK_spec

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
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {ι : Type} [Fintype ι]
    (v w : ι → K) :
    ∑ i, algebraMap K E (v i) * cj (algebraMap K E (w i)) = algebraMap K E (hf (conjK cj h) v w) := by
  simp only [hf, map_sum, map_mul, conjK_spec]
end PI.KLW
