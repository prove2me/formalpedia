-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:43.38694+00:00
-- url     : https://prove2.me/submissions/46677af9-a3ef-4424-8969-a030aebb2317

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re ^ 2 ≤ normSq v * normSq w := by
  have h1 : |(star v ⬝ᵥ w).re| ≤ ∑ k, ‖v k‖ * ‖w k‖ := by
    have e1 : |(star v ⬝ᵥ w).re| ≤ ‖star v ⬝ᵥ w‖ := by
      first
        | exact Complex.abs_re_le_norm _
        | exact RCLike.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
    have e2 : ‖star v ⬝ᵥ w‖ ≤ ∑ k, ‖star (v k) * w k‖ := by
      unfold dotProduct
      exact norm_sum_le _ _
    have e3 : ∑ k, ‖star (v k) * w k‖ = ∑ k, ‖v k‖ * ‖w k‖ := by
      simp [norm_mul, norm_star]
    linarith
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖v k‖) (fun k => ‖w k‖)
  have h3 : (star v ⬝ᵥ w).re ^ 2 ≤ (∑ k, ‖v k‖ * ‖w k‖) ^ 2 :=
    sq_le_sq.mpr (h1.trans (le_abs_self _))
  unfold normSq
  exact h3.trans h2
end ReciprocityTheory.MultiplicativeHeights
