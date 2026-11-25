-- Prove2me | solution 1 for PI.KLW.NO.fixed_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:55:39.676706+00:00
-- url     : https://prove2.me/submissions/5d569393-c81d-4f56-8c94-48b73455b0ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_fixed_rat
import Theorems.Thm_PI_KLW_NO_int_of_rat

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) {x : K} (hx : c x = x) (hO : x ∈ (algebraMap (𝓞 K) K).range) :
    ∃ m : ℤ, x = (m : K) := by
  obtain ⟨q, rfl⟩ := fixed_rat c hK hne hx
  obtain ⟨m, rfl⟩ := int_of_rat q hO
  exact ⟨m, by simp⟩
end PI.KLW.NO
