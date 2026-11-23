-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:53.469031+00:00
-- url     : https://prove2.me/submissions/ab11b744-6b1a-417f-b735-f5cdd500e7d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
theorem _root_.solution (P : ℂ_[l][X]) (hP : P.Monic) (x : ℂ_[l]) (h : ‖P.eval x‖ < 1) :
    ∃ a, P.IsRoot a ∧ ‖x - a‖ < 1 := by
  have hsplit : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP IsAlgClosed.card_roots_eq_natDegree
  by_contra hcon
  push Not at hcon
  have key : ∀ s : Multiset ℂ_[l], (∀ a ∈ s, 1 ≤ ‖x - a‖) →
      1 ≤ ‖((s.map fun a => X - C a).prod).eval x‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul]
      simp only [eval_sub, eval_X, eval_C]
      exact one_le_mul_of_one_le_of_one_le (hs a (Multiset.mem_cons_self _ _))
        (ih fun b hb => hs b (Multiset.mem_cons_of_mem hb))
  have := key P.roots (fun a ha => hcon a ((mem_roots hP.ne_zero).1 ha))
  rw [hsplit] at this
  linarith
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
