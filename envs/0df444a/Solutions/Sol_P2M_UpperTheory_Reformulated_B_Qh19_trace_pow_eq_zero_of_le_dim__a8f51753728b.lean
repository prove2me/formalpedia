-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:05.253832+00:00
-- url     : https://prove2.me/submissions/e742f353-491c-4494-8d37-9233faf68ebb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TracePowEqZeroOfLeDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim
theorem _root_.solution.{u_1} :
    ∀ {K : Type u_1}
    [inst : Field K] (r : ℕ) (N : Matrix (Fin r) (Fin r) K),
    (∀ (k : ℕ), (1 : ℕ) ≤ k → k ≤ r → (N ^ k).trace = (0 : K)) → ∀ (k : ℕ), (1 : ℕ) ≤ k → (N ^ k).trace = (0 : K) := by
  intro K _ r N h k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkr : k ≤ r
    · exact h k hk hkr
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + r := ⟨k - r - 1, by omega⟩
      have hd : N.charpoly.natDegree = r := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      have hc : N.charpoly.coeff r = 1 := by
        have := (Matrix.charpoly_monic N).coeff_natDegree
        rwa [hd] at this
      have hCH := Matrix.aeval_self_charpoly N
      rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, hc, one_smul] at hCH
      have h2 := congrArg (fun A => Matrix.trace (N ^ (m + 1) * A)) hCH
      simp only [mul_add, Finset.mul_sum, Matrix.mul_smul, ← pow_add, mul_zero, Matrix.trace_zero,
        Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul] at h2
      rw [Finset.sum_eq_zero, zero_add] at h2
      · exact h2
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [ih (m + 1 + i) (by omega) (by omega), smul_zero]
end UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim
