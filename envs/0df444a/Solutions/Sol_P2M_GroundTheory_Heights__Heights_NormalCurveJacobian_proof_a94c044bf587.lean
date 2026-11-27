-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalCurveJacobian_proof_a94c044bf587
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:11.022284+00:00
-- url     : https://prove2.me/submissions/9fe8407e-8486-49fe-bd6f-5d648fd2feda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurvePointDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCurveJacobian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_of_isDiscreteValuationRing_315fc3a6886b


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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormalCurveJacobian
theorem _root_.solution (hDVR : NormalCurvePointDVR.Statement) : NormalCurveJacobian.Statement := by
  intro σ _ I w hI hint hdim hw
  obtain ⟨hd, hdvr⟩ := hDVR σ I w hI hint hdim hw
  let : Algebra (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs (Algebra (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  have : IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs
      (IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  exact JacobianAtCurvePoint.exists_of_isDiscreteValuationRing I w hw (pointLocalRing I w)
    (by exact Ideal.Quotient.mk_surjective) (by exact Ideal.mk_ker)
end NormalCurveJacobian
end GroundTheory.Heights₂.Heights
