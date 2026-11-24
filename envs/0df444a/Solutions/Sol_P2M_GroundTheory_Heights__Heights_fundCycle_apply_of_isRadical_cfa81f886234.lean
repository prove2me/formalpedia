-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:29.533731+00:00
-- url     : https://prove2.me/submissions/ce37bb44-a239-4be6-89f7-41a9c96e329a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_eq_one_of_isRadical_c91ebf588e5e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) R)} (hJ : J.IsRadical) {W : Ideal (MvPolynomial (Fin n) R)}
    (hW : W ∈ (fundCycle J).support) : fundCycle J W = 1 := by
  classical
  have hval : fundCycle J W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  unfold fundCycle
  rw [Finsupp.onFinset_apply, if_pos hrel]
  exact localMult_eq_one_of_isRadical hJ hrel.1
end GroundTheory.Heights₂.Heights
