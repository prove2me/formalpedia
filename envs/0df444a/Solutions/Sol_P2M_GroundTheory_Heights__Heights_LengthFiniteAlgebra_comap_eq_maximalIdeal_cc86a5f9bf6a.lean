-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthFiniteAlgebra_comap_eq_maximalIdeal_cc86a5f9bf6a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:59.147084+00:00
-- url     : https://prove2.me/submissions/2f4cac4f-479d-4ed2-b7b2-04a8cffb86e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthFiniteAlgebra

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
open IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
namespace GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
theorem _root_.solution [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    P.comap (algebraMap O B) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
end GroundTheory.Heights₂.Heights.LengthFiniteAlgebra
