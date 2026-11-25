-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qm7_exists_common_multiple__e387a76b269a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:26.549071+00:00
-- url     : https://prove2.me/submissions/eb5ea5eb-df9f-4ba7-a9a1-0fb6207a31f2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qm7.exists_common_multiple
theorem _root_.solution.{u_2} :
    ∀ {ι : Type u_2} (s : Finset ι)
    (P : ι → ℕ → Prop),
    (∀ (i : ι) (a b : ℕ), P i a → a ∣ b → P i b) →
      (∀ i ∈ s, ∃ (a : ℕ), (0 : ℕ) < a ∧ P i a) → ∃ (d : ℕ), (0 : ℕ) < d ∧ ∀ i ∈ s, P i d := by
  intro ι s P hP h
  choose! a ha using h
  exact ⟨∏ i ∈ s, a i, Finset.prod_pos fun i hi => (ha i hi).1,
    fun i hi => hP i _ _ (ha i hi).2 (Finset.dvd_prod_of_mem a hi)⟩
end UpperTheory.Reformulated.B.Qm7.exists_common_multiple
