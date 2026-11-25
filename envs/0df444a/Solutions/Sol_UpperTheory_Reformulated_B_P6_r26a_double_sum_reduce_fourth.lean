-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_fourth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:06:37.848071+00:00
-- url     : https://prove2.me/submissions/e913da4d-8b74-4f6d-9f67-2e39a5bc0d86

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_DoubleSumReduceSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r26a
open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End
namespace UpperTheory.Reformulated.B.P6.r26a
theorem _root_.solution {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
      = ∑ b : Fin n, (if ε c = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ hac
    apply Finset.sum_eq_zero
    intro b _
    simp [hac]
  · intro h
    exact absurd (Finset.mem_univ c) h
end UpperTheory.Reformulated.B.P6.r26a
