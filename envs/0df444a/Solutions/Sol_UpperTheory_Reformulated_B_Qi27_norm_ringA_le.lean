-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qi27.norm_ringA_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:45:03.27651+00:00
-- url     : https://prove2.me/submissions/c1051b0e-d687-45b3-a057-69bb9681dc07

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi27
theorem _root_.solution :
    ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {x : ℂ_[l]}, x ∈ UpperTheory.Reformulated.B.Qi27.ringA l → ‖x‖ ≤ (1 : ℝ) := by
  intro l hl x hx
  unfold UpperTheory.Reformulated.B.Qi27.ringA at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨n, hn, -, h⟩ := hy
    have h1 : ‖y‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  | neg a _ ha => simpa using ha
  | mul a b _ _ ha hb =>
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
end UpperTheory.Reformulated.B.Qi27
