-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.pm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:46.964383+00:00
-- url     : https://prove2.me/submissions/eb5af13f-160b-454e-8b95-0193fe7bd744

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.LowA
theorem _root_.solution {ι : Type*} (s : Finset ι) (u : ι → R) (e : ι → ℕ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    ∏ i ∈ s, u i ^ e i = 1 ∨ ∏ i ∈ s, u i ^ e i = -1 := by
  classical
  have hpow : ∀ i, u i ^ e i = 1 ∨ u i ^ e i = -1 := fun i => by
    rcases hu i with h | h
    · left
      rw [h, one_pow]
    · rw [h]
      exact neg_one_pow_eq_or R (e i)
  have hmul : ∀ a b : R, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) → (a * b = 1 ∨ a * b = -1) := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  refine Finset.induction_on s ?_ ?_
  · left
    exact Finset.prod_empty
  · intro a t ha ih
    rw [Finset.prod_insert ha]
    exact hmul _ _ (hpow a) ih
end PI.OddDualWeyl.LowA
