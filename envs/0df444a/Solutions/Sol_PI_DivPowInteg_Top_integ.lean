-- Prove2me | solution 1 for PI.DivPowInteg.Top.integ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:56:13.088974+00:00
-- url     : https://prove2.me/submissions/5eb3ab9d-090f-4296-b2fb-ca38b7f14f69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
import Theorems.Thm_PI_DivPowInteg_Top_dpow_zero
import Theorems.Thm_PI_DivPowInteg_Top_dpow_add
import Theorems.Thm_PI_DivPowInteg_Top_dpow_C_succ
import Theorems.Thm_PI_DivPowInteg_Top_dpow_X_mul
import Theorems.Thm_PI_DivPowInteg_Top_good_X_mul
import Theorems.Thm_PI_DivPowInteg_Top_good_dL
import Theorems.Thm_PI_DivPowInteg_Top_good_dR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.DivPowInteg PI.DivPowInteg.Top
open PI.DivPowInteg.Gen
variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]
namespace PI.DivPowInteg.Top
theorem _root_.solution (h1 : PowXL) (h2 : PowXR) (L : Submodule A K) (κ : I → J → K)
    (hκ : ∀ i j, κ i j ∈ L) (P : MvPolynomial (I ⊕ J) A) :
    ∀ n, Good L n (dpow κ n (map (algebraMap A K) P)) := by
  classical
  have h0 : ∀ P : MvPolynomial (I ⊕ J) A, Good L 0 (map (algebraMap A K) P) := by
    intro P m
    rw [MvPolynomial.coeff_map, pow_zero]
    exact Submodule.algebraMap_mem _
  refine MvPolynomial.induction_on
    (motive := fun P => ∀ n, Good L n (dpow κ n (map (algebraMap A K) P))) P ?_ ?_ ?_
  · intro a n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (C a)
    | succ k =>
      rw [MvPolynomial.map_C, dpow_C_succ]
      intro m
      rw [MvPolynomial.coeff_zero]
      exact Submodule.zero_mem _
  · intro p q hp hq n m
    rw [map_add, dpow_add, MvPolynomial.coeff_add]
    exact Submodule.add_mem _ (hp n m) (hq n m)
  · intro p s hp n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (p * X s)
    | succ k =>
      rw [map_mul, MvPolynomial.map_X, mul_comm]
      cases s with
      | inl i =>
        rw [dpow_X_mul κ (Sum.inl i) (dL κ i) (map (algebraMap A K) p) k
          (h1 K I J κ i (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dL L κ hκ k i _ (hp k) m)
      | inr j =>
        rw [dpow_X_mul κ (Sum.inr j) (dR κ j) (map (algebraMap A K) p) k
          (h2 K I J κ j (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dR L κ hκ k j _ (hp k) m)
end PI.DivPowInteg.Top
