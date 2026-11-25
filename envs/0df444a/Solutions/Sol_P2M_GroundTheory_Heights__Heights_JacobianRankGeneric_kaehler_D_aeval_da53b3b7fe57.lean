-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_kaehler_D_aeval_da53b3b7fe57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:23.95904+00:00
-- url     : https://prove2.me/submissions/ec826954-1759-439d-84c9-5d6b1dd09ebe

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric

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
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace JacobianRankGeneric
theorem _root_.solution {σ K : Type*} [Fintype σ] [Field K] [Algebra ℂ K] (x : σ → K)
    (f : MvPolynomial σ ℂ) :
    KaehlerDifferential.D ℂ K (aeval x f) =
      ∑ l, aeval x (pderiv l f) • KaehlerDifferential.D ℂ K (x l) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, add_smul]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, Finset.smul_sum, smul_smul, map_add, add_smul,
      Finset.sum_add_distrib, pderiv_X, smul_eq_mul, Pi.single_apply]
    rw [add_left_inj]
    simp [apply_ite, ite_smul]
end JacobianRankGeneric
end GroundTheory.Heights₂.Heights
