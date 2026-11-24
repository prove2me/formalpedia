-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:05.335125+00:00
-- url     : https://prove2.me/submissions/fd0927ff-4a3c-4c87-b8d9-d872020deb70

import Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSelfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (P : MvPolynomial (Fin ν × ι) ℂ) (hP : P ≠ 0) : fischer P P ≠ 0 := by
  intro h0
  have hsum : fischer P P = ((∑ A ∈ P.support,
      ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold fischer
    rw [Finset.union_self]
    push_cast
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Finsupp.prod]
    push_cast
    ring
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hP (MvPolynomial.support_eq_empty.mp h))
  have hpos : 0 < ∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
    refine Finset.sum_pos (fun A hA => ?_) hne
    have h1 : coeff A P ≠ 0 := MvPolynomial.mem_support_iff.mp hA
    have h2 : 0 < ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun _ _ => Nat.factorial_pos _
    have h3 : 0 < ‖coeff A P‖ ^ 2 := by positivity
    positivity
  rw [hsum] at h0
  have h4 : (∑ A ∈ P.support, ‖coeff A P‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) = 0 := by
    exact_mod_cast h0
  linarith
end ReciprocityTheory.PGsh
