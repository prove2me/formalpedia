-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:55:52.873928+00:00
-- url     : https://prove2.me/submissions/51564883-e4f8-44b5-a7b2-4cd1c4255a72

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sgn_mul_swap
import Theorems.Thm_Formalism_REAL_eq_zero_of_eq_neg_self_of_algebra_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (P Q X : Equiv.Perm (Fin t) → A)
    (hX : ∀ τ, X (τ * s) = X τ) (hPQ : ∀ τ, P (τ * s) - Q τ = X τ) :
    ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * Q τ = -∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ := by
  have hz : ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * X τ = 0 := by
    have h1 : ∑ τ, ((Equiv.Perm.sign (τ * s) : ℤ) : A) * X (τ * s) =
        ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * X τ :=
      Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun τ => rfl)
    simp only [hX, sgn_mul_swap s hs, neg_mul, Finset.sum_neg_distrib] at h1
    exact eq_zero_of_eq_neg_self_of_algebra_complex _ h1.symm
  have h2 : ∑ τ, ((Equiv.Perm.sign (τ * s) : ℤ) : A) * P (τ * s) =
      ∑ τ, ((Equiv.Perm.sign τ : ℤ) : A) * P τ :=
    Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun τ => rfl)
  have hP : ∀ τ, P (τ * s) = Q τ + X τ := fun τ => by rw [← hPQ τ]; abel
  simp only [hP, sgn_mul_swap s hs, neg_mul, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, hz] at h2
  rw [← h2]
  simp only [neg_zero, add_zero, neg_neg]
end PI.UnitaryGroupMassFormula.QmMove
