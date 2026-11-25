-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_DoubleSumDiagonalOffDiagonal_main__4b070f59598e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:35.990218+00:00
-- url     : https://prove2.me/submissions/1b7438cb-0c8f-48c2-b216-291dd79fcd6c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FirstStatementB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal
theorem _root_.solution.{u_3} :
    ∀ {n : ℕ} {M : Type u_3} [inst : AddCommMonoid M]
    (F : Fin n → Fin n → M),
    ∑ a : Fin n, ∑ b : Fin n, F a b =
      ∑ a : Fin n, F a a + ∑ a : Fin n, ∑ b : Fin n, if a < b then F a b + F b a else (0 : M) := by
  intro n M _ F
  have h1 : ∀ a b : Fin n, F a b = (if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hd : ∀ a : Fin n, (∑ b : Fin n, if a = b then F a b else 0) = F a a := by
    intro a
    rw [Finset.sum_ite_eq]
    simp
  have hc : (∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0)
      = ∑ a : Fin n, ∑ b : Fin n, if a < b then F b a else 0 := by
    rw [Finset.sum_comm]
  calc ∑ a : Fin n, ∑ b : Fin n, F a b
      = ∑ a : Fin n, ∑ b : Fin n, ((if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b
    _ = ∑ a : Fin n, F a a + ((∑ a : Fin n, ∑ b : Fin n, if a < b then F a b else 0)
        + ∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0) := by
        simp only [Finset.sum_add_distrib, hd]
    _ = _ := by
        rw [hc, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
end UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal
