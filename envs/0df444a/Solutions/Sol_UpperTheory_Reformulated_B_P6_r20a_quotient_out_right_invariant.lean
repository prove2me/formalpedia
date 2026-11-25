-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r20a.quotient_out_right_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:50.296622+00:00
-- url     : https://prove2.me/submissions/38c3a8c8-5781-47ea-afcc-796f3876fbdd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_QuotientOutRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r20a
namespace UpperTheory.Reformulated.B.P6.r20a
theorem _root_.solution {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ (x k : H), k ∈ K → u (x * k) = u x) (x : H) :
    u (Quotient.out (x : H ⧸ K)) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk]
  exact hu x k k.2
end UpperTheory.Reformulated.B.P6.r20a
