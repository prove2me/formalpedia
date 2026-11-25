-- Prove2me | solution 1 for PI.Residue.factorization_multiset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:29.22747+00:00
-- url     : https://prove2.me/submissions/553500b9-bf89-4859-8ce5-04bc449cf536

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]
namespace PI.Residue
theorem _root_.solution (m : Multiset ℕ) (h : ∀ x ∈ m, x ≠ 0) (p : ℕ) :
    m.prod.factorization p = (m.map (fun x => x.factorization p)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hs' : s.prod ≠ 0 := by
      intro h0
      exact hs 0 (Multiset.prod_eq_zero_iff.mp h0) rfl
    rw [Multiset.prod_cons, Nat.factorization_mul ha hs', Multiset.map_cons, Multiset.sum_cons,
      Finsupp.add_apply, ih hs]
end PI.Residue
