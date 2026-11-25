-- Prove2me | solution 1 for PI.DivPowInteg.Top.good_dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:06.496715+00:00
-- url     : https://prove2.me/submissions/731c7b1e-e455-4299-994d-312643269b3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_NatMulFactorialBound
import Theorems.Thm_PI_DivPowInteg_Top_good_smul_pderiv

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
theorem _root_.solution (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (i : I)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dL κ i Q) := by
  intro m
  have e : (dL κ i Q).coeff m = ∑ j, κ i j * coeff m (pderiv (Sum.inr j) Q) := by
    simp [dL, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m
end PI.DivPowInteg.Top
