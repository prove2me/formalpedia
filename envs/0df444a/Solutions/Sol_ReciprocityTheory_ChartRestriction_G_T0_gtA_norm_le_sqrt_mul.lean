-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtA_norm_le_sqrt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:15.295666+00:00
-- url     : https://prove2.me/submissions/95bc532f-4898-4973-b91a-5ead22cd3050

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM : ∀ i, ‖x i‖ ≤ ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := fun i =>
    norm_le_pi_norm (EuclideanSpace.equiv (Fin n) ℝ x) i
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin n, ‖EuclideanSpace.equiv (Fin n) ℝ x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => by gcongr; exact hM i
    _ = Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
end ReciprocityTheory.ChartRestriction.G.T0
