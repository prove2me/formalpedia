-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:01.933149+00:00
-- url     : https://prove2.me/submissions/ceea688f-f0c4-4259-a412-662a8539adf4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qe24.spanS_induction
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {n : ℕ} {x : Fin n → V} {p : V → Prop},
      p (0 : V) →
        (∀ (a b : V), p a → p b → p (a + b)) →
          (∀ c ∈ S, ∀ (a : V), p a → p (c • a)) → (∀ (i : Fin n), p (x i)) → ∀ v ∈ UpperTheory.Reformulated.B.Qe24.spanS S x, p v := by
  intro K V _ _ _ _ S n x p h0 hadd hsmul hx v hv
  unfold UpperTheory.Reformulated.B.Qe24.spanS at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hx i
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c.1 c.2 a ha
end UpperTheory.Reformulated.B.Qe24.spanS_induction
