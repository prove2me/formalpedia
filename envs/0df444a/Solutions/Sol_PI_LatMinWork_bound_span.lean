-- Prove2me | solution 1 for PI.LatMinWork.bound_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:52.332278+00:00
-- url     : https://prove2.me/submissions/4252f64e-c918-4041-8e8a-083eb55907ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LatMinWork
variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]
namespace PI.LatMinWork
theorem _root_.solution (B : V → V → ℚ_[p])
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (S : Set V) (w : V) (M : ℝ) (hM : 0 ≤ M) (hS : ∀ b ∈ S, ‖B b w‖ ≤ M) :
    ∀ v ∈ Submodule.span ℤ_[p] S, ‖B v w‖ ≤ M := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h0 : B 0 w = 0 := by simpa using hsm 0 0 w
    rw [h0, norm_zero]; exact hM
  | add x y _ _ hx hy =>
    rw [hadd]
    exact (show ‖B x w + B y w‖ ≤ max ‖B x w‖ ‖B y w‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [hsm, norm_mul]
    have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
      first
        | exact c.2
        | simpa using PadicInt.norm_le_one c
    calc ‖(c : ℚ_[p])‖ * ‖B x w‖ ≤ 1 * ‖B x w‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hx
end PI.LatMinWork
