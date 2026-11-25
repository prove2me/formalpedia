-- Prove2me | solution 1 for PI.DivPowInteg.Gen.gdelta_X_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:23.81494+00:00
-- url     : https://prove2.me/submissions/9a58b847-4302-4280-99c6-77855e3da2ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow
import Theorems.Thm_PI_DivPowInteg_Gen_gdelta_apply
import Theorems.Thm_PI_DivPowInteg_Gen_dL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Gen
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
namespace PI.DivPowInteg.Gen
theorem _root_.solution (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ j, pderiv (Sum.inr j) (X (Sum.inl i) * R) = X (Sum.inl i) * pderiv (Sum.inr j) R := by
    intro j
    rw [Derivation.leibniz, pderiv_X_of_ne Sum.inl_ne_inr, smul_zero, add_zero, smul_eq_mul]
  have h2 : ∀ (i' : I) (S : MvPolynomial (I ⊕ J) K), pderiv (Sum.inl i') (X (Sum.inl i) * S) =
      X (Sum.inl i) * pderiv (Sum.inl i') S + if i' = i then S else 0 := by
    intro i' S
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases h : i' = i
    · subst h
      rw [pderiv_X_self, mul_one, if_pos rfl]
    · rw [pderiv_X_of_ne (fun e => h (Sum.inl_injective e).symm), mul_zero, add_zero, if_neg h, add_zero]
  have hΔ : ∀ S : MvPolynomial (I ⊕ J) K,
      gdelta κ S = ∑ j, ∑ i', κ i' j • pderiv (Sum.inl i') (pderiv (Sum.inr j) S) := by
    intro S
    rw [gdelta_apply, Finset.sum_comm]
  rw [hΔ, hΔ, dL_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, Finset.mul_sum]
  simp only [h2, smul_add, Finset.sum_add_distrib, mul_smul_comm, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
end PI.DivPowInteg.Gen
