-- Prove2me | solution 1 for PI.RL.W.derivation_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:41.262556+00:00
-- url     : https://prove2.me/submissions/41b65935-10da-4315-a7df-57962b21a1e8

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
theorem _root_.solution {ι : Type*} {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
    [Algebra R A] [Module R M] (s : Finset ι) (D : ι → Derivation R A M) (x : A) :
    (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
end PI.RL.W
