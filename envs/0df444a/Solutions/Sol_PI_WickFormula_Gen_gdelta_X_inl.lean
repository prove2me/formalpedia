-- Prove2me | solution 1 for PI.WickFormula.Gen.gdelta_X_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:04.468583+00:00
-- url     : https://prove2.me/submissions/69255ab4-c76b-4757-8ded-06254f9136a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow
import Theorems.Thm_PI_WickFormula_Gen_gdelta_apply
import Theorems.Thm_PI_WickFormula_Gen_dL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.WickFormula.Gen
theorem _root_.solution (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ i' j, pderiv (Sum.inl i') (pderiv (Sum.inr j) (X (Sum.inl i) * R)) =
      X (Sum.inl i) * pderiv (Sum.inl i') (pderiv (Sum.inr j) R) +
        (if i' = i then pderiv (Sum.inr j) R else 0) := by
    intro i' j
    rw [pderiv_mul, pderiv_X_of_ne (by simp), zero_mul, zero_add, pderiv_mul, pderiv_X]
    by_cases h : i' = i
    · subst h
      simp [add_comm]
    · simp [h, Ne.symm h]
  rw [gdelta_apply, gdelta_apply, dL_apply]
  simp only [h1, smul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_smul_comm, smul_ite,
    smul_zero]
  congr 1
  rw [Finset.sum_comm]
  simp
end PI.WickFormula.Gen
