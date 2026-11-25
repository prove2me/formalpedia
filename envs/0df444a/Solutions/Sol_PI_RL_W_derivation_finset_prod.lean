-- Prove2me | solution 1 for PI.RL.W.derivation_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:27.828879+00:00
-- url     : https://prove2.me/submissions/b15f6329-19bd-4006-8ea2-ee8166881388

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_DetDer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RL PI.RL.W
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace PI.RL.W
theorem _root_.solution {ι : Type*} [DecidableEq ι] (D : Derivation R S S) (f : ι → S) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  have hne : ∀ i ∈ s, i ≠ a := fun i hi h => ha (h ▸ hi)
  have h0 : Function.update f a (D (f a)) a = D (f a) := by simp
  have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j :=
    Finset.prod_congr rfl fun j hj => Function.update_of_ne (hne j hj) _ _
  have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
      f a * ∏ j ∈ s, Function.update f i (D (f i)) j := fun i hi => by
    rw [Finset.prod_insert ha, Function.update_of_ne (hne i hi).symm]
  rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha, h0, h1,
    Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
  ring
end PI.RL.W
