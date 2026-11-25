-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_anti_daa7b5be1ca9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:45.568367+00:00
-- url     : https://prove2.me/submissions/962d233c-695f-4ba1-8518-01e3441ccb6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric

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
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
namespace GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
theorem _root_.solution {R : Type*} [CommRing R] {K K' : Ideal R} (h : K ≤ K') :
    ringKrullDim (R ⧸ K') ≤ ringKrullDim (R ⧸ K) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)
end GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric
