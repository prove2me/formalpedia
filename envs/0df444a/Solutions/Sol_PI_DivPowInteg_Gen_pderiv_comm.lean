-- Prove2me | solution 1 for PI.DivPowInteg.Gen.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:47.950108+00:00
-- url     : https://prove2.me/submissions/8e81efed-7de0-45fe-9478-fb2ebf1c767b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenPow

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
theorem _root_.solution (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have hc : ∀ (c d : I ⊕ J) (n : I ⊕ J),
      pderiv c (Pi.single (M := fun _ => MvPolynomial (I ⊕ J) K) d 1 n) = 0 := by
    intro c d n
    rw [Pi.single_apply]
    split_ifs <;> simp
  induction p using MvPolynomial.induction_on with
  | C x => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, hc, hp, mul_zero, zero_add]
    ring
end PI.DivPowInteg.Gen
