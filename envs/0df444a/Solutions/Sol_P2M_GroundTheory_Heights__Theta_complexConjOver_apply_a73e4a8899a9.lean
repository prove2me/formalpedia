-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_complexConjOver_apply_a73e4a8899a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:33.310025+00:00
-- url     : https://prove2.me/submissions/c681defb-a91d-4e19-8745-296a8c6a40a5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum

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
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (x : E) :
    haveI := isCMField F E
    complexConjOver F E x = IsCMField.complexConj E x := rfl
end GroundTheory.Heights₂.Theta
