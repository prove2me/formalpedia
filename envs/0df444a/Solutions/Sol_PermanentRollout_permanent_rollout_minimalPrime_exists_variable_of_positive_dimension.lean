-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_minimalPrime_exists_variable_of_positive_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/d689fca9-d395-451c-add1-c2e21fd9d8b6

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_minimalPrime_isHomogeneous
import Theorems.Thm_PermanentRollout_permanent_rollout_homogeneousPrime_le_idealOfVars
import Theorems.Thm_PermanentRollout_permanent_rollout_idealOfVars_isMaximal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (hdimension :
      (0 : WithBot ℕ∞) <
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ I))
    (p : Ideal (MvPolynomial (Fin m) ℂ))
    (hp : p ∈ I.minimalPrimes) :
    ∃ i : Fin m, MvPolynomial.X i ∉ p := by
  classical
  by_contra hnone
  simp only [not_exists, not_not] at hnone
  have hvertex_le : MvPolynomial.idealOfVars (Fin m) ℂ ≤ p := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro f ⟨i, rfl⟩
    exact hnone i
  have hp_vertex : p = MvPolynomial.idealOfVars (Fin m) ℂ :=
    le_antisymm
      (permanent_rollout_homogeneousPrime_le_idealOfVars p hp.isPrime
        (permanent_rollout_minimalPrime_isHomogeneous hI hp))
      hvertex_le
  have hallmaximal :
      ∀ q ∈ I.minimalPrimes, q.IsMaximal := by
    intro q hq
    have hq_vertex : q ≤ MvPolynomial.idealOfVars (Fin m) ℂ :=
      permanent_rollout_homogeneousPrime_le_idealOfVars q hq.isPrime
        (permanent_rollout_minimalPrime_isHomogeneous hI hq)
    have hq_p : q ≤ p := hp_vertex.symm ▸ hq_vertex
    have hp_q : p ≤ q := hp.2 ⟨hq.isPrime, hq.le⟩ hq_p
    have hqeq : q = MvPolynomial.idealOfVars (Fin m) ℂ :=
      (le_antisymm hq_p hp_q).trans hp_vertex
    rw [hqeq]
    exact permanent_rollout_idealOfVars_isMaximal m
  have hzero :
      Ring.KrullDimLE 0 (MvPolynomial (Fin m) ℂ ⧸ I) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
      hallmaximal
  have hnonpositive :
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ I) ≤
        (0 : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp hzero
  exact (not_lt_of_ge hnonpositive) hdimension
end PermanentRollout
