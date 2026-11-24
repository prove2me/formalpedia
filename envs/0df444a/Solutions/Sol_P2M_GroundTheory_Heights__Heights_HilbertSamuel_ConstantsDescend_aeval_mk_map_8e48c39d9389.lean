-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_aeval_mk_map_8e48c39d9389
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:35.994321+00:00
-- url     : https://prove2.me/submissions/91361457-6491-4605-8b53-73048f13ac0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution (θ : B) (I : Ideal A) (P : A[X]) :
    aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (aeval θ P) := by
  rw [aeval_map_algebraMap]
  exact aeval_algHom_apply (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))) θ P
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
