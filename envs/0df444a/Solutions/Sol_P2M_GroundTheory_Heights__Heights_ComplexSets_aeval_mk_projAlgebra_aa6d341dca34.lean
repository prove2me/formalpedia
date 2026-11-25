-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_aeval_mk_projAlgebra_aa6d341dca34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:53.77819+00:00
-- url     : https://prove2.me/submissions/f81135c5-cebd-4b65-886d-4502070309f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (G : Polynomial (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    letI := projAlgebra J A
    Polynomial.aeval (Ideal.Quotient.mk J p) G =
      Ideal.Quotient.mk J (Polynomial.eval₂ (pullback A).toRingHom p G) := by
  let _ := projAlgebra J A
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  rfl
end GroundTheory.Heights₂.Heights.ComplexSets
