-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r26a.double_sum_reduce_third
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:30.833537+00:00
-- url     : https://prove2.me/submissions/c0db6f17-b41c-41fa-a746-7beee9f98b80

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
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = b then E a b * E c a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε d then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    simp [Ne.symm hbd]
  · intro h
    exact absurd (Finset.mem_univ d) h
end UpperTheory.Reformulated.B.P6.r26a
