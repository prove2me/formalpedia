-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r26a.commutator_casimir_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:06.322996+00:00
-- url     : https://prove2.me/submissions/2d9f7c55-7a75-4352-99b4-d821a402120e

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
    (E : Fin n → Fin n → Module.End ℂ V) (hK : PositivityTheory.D.DSIC.KRel ε E) {c d : Fin n} (hcd : ε c = ε d)
    (a b : Fin n) :
    E c d * (if ε a = ε b then E a b * E b a else 0) - (if ε a = ε b then E a b * E b a else 0) * E c d
      = ((if ε a = ε b then (if d = a then E c b * E b a else 0) else 0)
          - (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
        + ((if ε a = ε b then (if d = b then E a b * E c a else 0) else 0)
          - (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0)) := by
  by_cases h : ε a = ε b
  · simp only [if_pos h]
    have h1 : E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) :=
      hK a b c d h hcd
    have h2 : E b a * E c d - E c d * E b a = (if a = c then E b d else 0) - (if d = b then E c a else 0) :=
      hK b a c d h.symm hcd
    have key : E c d * (E a b * E b a) - E a b * E b a * E c d
        = -((E a b * E c d - E c d * E a b) * E b a) - E a b * (E b a * E c d - E c d * E b a) := by
      noncomm_ring
    rw [key, h1, h2]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    abel
  · simp only [if_neg h]
    simp
end UpperTheory.Reformulated.B.P6.r26a
