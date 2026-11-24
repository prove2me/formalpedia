-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yzd3.phi_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:35.407582+00:00
-- url     : https://prove2.me/submissions/6ab63202-12fa-4a78-a277-51c72e23fffa

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PhiMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yzd3
theorem _root_.solution :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd3.Phi a R * UpperTheory.Reformulated.B.Yzd3.Phi a R = (-1 : R) ^ (a - (1 : ℕ)) • (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i k
  have hi := i.2
  have hk := k.2
  have hj : a - 1 - (i : ℕ) < a := by omega
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.Yzd3.Phi, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨a - 1 - (i : ℕ), hj⟩ : Fin a)]
  · have h1 : (i : ℕ) + (a - 1 - (i : ℕ)) + 1 = a := by omega
    dsimp only
    rw [if_pos h1]
    by_cases hik : i = k
    · subst hik
      have h2 : (a - 1 - (i : ℕ)) + (i : ℕ) + 1 = a := by omega
      rw [if_pos h2, if_pos rfl, mul_one, ← pow_add]
      congr 1
      omega
    · have h2 : ¬ ((a - 1 - (i : ℕ)) + (k : ℕ) + 1 = a) := by
        intro h
        exact hik (Fin.ext (by omega))
      rw [if_neg h2, if_neg hik, mul_zero, mul_zero]
  · intro j _ hne
    have h1 : ¬ ((i : ℕ) + (j : ℕ) + 1 = a) := by
      intro h
      exact hne (Fin.ext (by simp only []; omega))
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end UpperTheory.Reformulated.B.Yzd3
