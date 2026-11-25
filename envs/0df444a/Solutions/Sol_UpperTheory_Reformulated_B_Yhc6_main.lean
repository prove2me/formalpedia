-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yhc6.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:06:43.792983+00:00
-- url     : https://prove2.me/submissions/6f3ab455-a200-4afa-ae13-9dd17dd3a9cb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsRestSide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yhc6
theorem _root_.solution :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (m : ℕ),
      ((↑g : Matrix (Fin n) (Fin n) k) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) k)) ^ m =
        (↑g : Matrix (Fin n) (Fin n) k) * x ^ m * (↑g⁻¹ : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ _ _ n g x m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
end UpperTheory.Reformulated.B.Yhc6
