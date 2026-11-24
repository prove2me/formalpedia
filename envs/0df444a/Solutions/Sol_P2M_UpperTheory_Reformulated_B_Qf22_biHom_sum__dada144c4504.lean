-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf22_biHom_sum__dada144c4504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:10.35029+00:00
-- url     : https://prove2.me/submissions/6afb8c9f-5e06-47bc-ae64-b1d8688bfc1c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf22.biHom_sum
theorem _root_.solution.{u_1} :
    ∀ {K ι κ : Type} [inst : Field K] [Fintype κ] {α : Type u_1} {d : ℕ} (s : Finset α)
      (F : α → MvPolynomial κ (MvPolynomial ι K)),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf22.biHom d (F a)) → UpperTheory.Reformulated.B.Qf22.biHom d (∑ a ∈ s, F a) := by
  intro K ι κ _ _ α d s F h β n hne
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum] at hne
  obtain ⟨a, ha, hna⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h a ha β n hna
end UpperTheory.Reformulated.B.Qf22.biHom_sum
