-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdB.quad_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:24.453097+00:00
-- url     : https://prove2.me/submissions/8d71e34e-3fe4-4e0a-b55e-a940f03d65c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdB
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdB
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (n : ℝ) * n * (‖v‖ * ‖H‖ * ‖v‖) := by
  have hvi : ∀ i, ‖v i‖ ≤ ‖v‖ := fun i => norm_le_pi_norm v i
  have hH : ∀ i j, ‖H i j‖ ≤ ‖H‖ := fun i j => norm_entry_le_entrywise_sup_norm H
  have key : ∀ i, ‖star (v i) * ∑ j, H i j * v j‖ ≤ ∑ _j : Fin n, ‖v‖ * ‖H‖ * ‖v‖ := by
    intro i
    rw [norm_mul, norm_star]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    have h1 := mul_le_mul (hH i j) (hvi j) (norm_nonneg _) (norm_nonneg _)
    calc ‖v i‖ * (‖H i j‖ * ‖v j‖) ≤ ‖v‖ * (‖H‖ * ‖v‖) :=
          mul_le_mul (hvi i) h1 (by positivity) (norm_nonneg _)
      _ = ‖v‖ * ‖H‖ * ‖v‖ := by ring
  have e : star v ⬝ᵥ (H *ᵥ v) = ∑ i, star (v i) * ∑ j, H i j * v j := by
    simp only [dotProduct, mulVec, Pi.star_apply]
  rw [e]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => key i).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.DS.S7.IdB
