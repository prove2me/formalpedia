-- Prove2me | solution 1 for PI.WickFormula.Gen.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:16:22.413804+00:00
-- url     : https://prove2.me/submissions/be11c9e2-7480-43b9-b19b-e810211b6d0f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_GenPow

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
theorem _root_.solution (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have h : ⁅(pderiv a : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K)),
      (pderiv b : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro c
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply, Derivation.zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K) =>
    D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  exact sub_eq_zero.mp h2
end PI.WickFormula.Gen
