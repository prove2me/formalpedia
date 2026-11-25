-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:09:54.815436+00:00
-- url     : https://prove2.me/submissions/2126f6f1-5dd8-4215-9f25-920391964eff

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
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = a then E c b * E b a else 0) else 0))
      = ∑ b : Fin n, (if ε d = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single d]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ had
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm had]
  · intro h
    exact absurd (Finset.mem_univ d) h
end UpperTheory.Reformulated.B.P6.r26a
