-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qj19_lin_bound__4cd42ebca5d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:26.548322+00:00
-- url     : https://prove2.me/submissions/f687f18f-3857-4675-b6ea-4a5cdbb6d791

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LinBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qj19.lin_bound
theorem _root_.solution.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ),
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ (i j : ι), ‖B i j‖ ≤ C) → ‖(L : Matrix ι ι ℂ → ℂ) B‖ ≤ K * C := by
  intro ι _ _ L
  refine ⟨∑ i, ∑ j, ‖L (Matrix.single i j 1)‖, by positivity, fun B C hB => ?_⟩
  have h : L B = ∑ i, ∑ j, B i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hB i j) (norm_nonneg _)
end UpperTheory.Reformulated.B.Qj19.lin_bound
