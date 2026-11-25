-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isProjPrime_3532aee1cba7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:19.209696+00:00
-- url     : https://prove2.me/submissions/87d81e27-598d-4a7d-8cc7-2bdd7aac7725

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormExists

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
theorem _root_.solution {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) {f : MvPolynomial (Fin n) F}
    (hf : f ∈ P) : constantCoeff f = 0 := by
  by_contra h
  have h0 : homogeneousComponent 0 f ∈ P := hP.isHomog f hf 0
  rw [homogeneousComponent_zero] at h0
  apply hP.isPrime.ne_top
  refine Ideal.eq_top_of_isUnit_mem _ h0 ?_
  have hc : coeff 0 f ≠ 0 := by simpa [constantCoeff] using h
  exact hc.isUnit.map C
end GroundTheory.Heights₂.Heights
