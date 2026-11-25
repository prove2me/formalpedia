-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ConservationOfDegree_proof_db64cf607e58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:18.3865+00:00
-- url     : https://prove2.me/submissions/8befb811-3c81-4e2b-aca9-136e729840b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsNefGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreHilbertFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreCycleDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PConservationOfDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace ConservationOfDegree
theorem _root_.solution (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} := by
  intro S _ _ F _ _ _ Ω _ _ _ _ N x M 𝔪 h𝔪 qq hq hconst hsub
  have h1 := hA S F Ω N x M 𝔪 h𝔪 qq hq hconst hsub
  have h2 := hB S F Ω N x M 𝔪 h𝔪 qq hq hconst hsub
  rw [interNum]
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [h1, h2] with c e1 e2
  rw [e1, e2]
end ConservationOfDegree
end GroundTheory.Heights₂.Heights.Kleiman
