-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:33.003896+00:00
-- url     : https://prove2.me/submissions/9c49394d-8498-465a-b10f-2b1dd00d77e4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PhiMulTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yzd2
theorem _root_.solution :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd2.Phi a R * (UpperTheory.Reformulated.B.Yzd2.Phi a R).transpose = (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, UpperTheory.Reformulated.B.Yzd2.Phi, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst h
    have hi := i.isLt
    let k : Fin a := ⟨a - 1 - (i : ℕ), by omega⟩
    have hk : (k : ℕ) = a - 1 - (i : ℕ) := rfl
    rw [Finset.sum_eq_single k]
    · have h1 : (i : ℕ) + (k : ℕ) + 1 = a := by omega
      rw [if_pos h1, if_pos rfl, ← mul_pow]
      simp
    · intro b _ hb
      have h1 : ¬ ((i : ℕ) + (b : ℕ) + 1 = a) := by
        intro h2
        apply hb
        ext
        omega
      simp [h1]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : (i : ℕ) + (k : ℕ) + 1 = a
    · have h2 : ¬ ((j : ℕ) + (k : ℕ) + 1 = a) := by
        intro h2
        apply h
        ext
        omega
      simp [h2]
    · simp [h1]
end UpperTheory.Reformulated.B.Yzd2
