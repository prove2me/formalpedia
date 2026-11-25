-- Prove2me | solution 1 for PI.DIP.NormOne.conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:57.426514+00:00
-- url     : https://prove2.me/submissions/8e37b5fe-28c1-4191-b870-c821c5629bfa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne
import Theorems.Thm_PI_DIP_NormOne_map_mem_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace PI.DIP.NormOne
theorem _root_.solution (c : E →+* E) (hc : ∀ x, c (c x) = x) {A A' B B' : Submodule (𝓞 E) E}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) (hB' : ∀ x, x ∈ B' ↔ c x ∈ A') :
    ∀ x, x ∈ B * B' ↔ c x ∈ A * A' := by
  intro x
  constructor
  · intro hx
    exact map_mem_mul c (fun p hp => (hB p).1 hp) (fun p hp => (hB' p).1 hp) x hx
  · intro hx
    have := map_mem_mul c (fun p hp => (hB (c p)).2 (by rwa [hc]))
      (fun p hp => (hB' (c p)).2 (by rwa [hc])) (c x) hx
    rwa [hc] at this
end PI.DIP.NormOne
