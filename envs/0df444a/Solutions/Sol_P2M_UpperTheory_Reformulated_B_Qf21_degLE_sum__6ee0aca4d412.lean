-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf21_degLE_sum__6ee0aca4d412
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:09.657838+00:00
-- url     : https://prove2.me/submissions/a66105e8-c367-4635-bc6f-6e9ad72688b1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf21.degLE_sum
theorem _root_.solution.{u_1} :
    ∀ {κ R : Type} [inst : CommRing R] {α : Type u_1} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf21.degLE W n (F a)) → UpperTheory.Reformulated.B.Qf21.degLE W n (∑ a ∈ s, F a) := by
  intro κ R _ α W n s F h β hβ
  rw [MvPolynomial.coeff_sum] at hβ
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact h a ha β hne
end UpperTheory.Reformulated.B.Qf21.degLE_sum
