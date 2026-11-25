-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_embedding_algebraMap_conj_473ce874b5b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:03.06924+00:00
-- url     : https://prove2.me/submissions/0ccb71c2-f14e-47c8-a558-024918fbb160

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_embedding_conj_e96b6af5af35
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField GroundTheory.Automorphic
variable (F E : Type*) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {F E}
variable (F E)
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (φ : E →+* ℂ) (c : F) :
    starRingEnd ℂ (φ (algebraMap F E c)) = φ (algebraMap F E c) := by
  rw [← embedding_conj F E, conj_algebraMap]
end GroundTheory.Heights₂.Theta
