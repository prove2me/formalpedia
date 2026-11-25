-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelFibre_continuous_firstCoords_380cb0872c21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:59.838745+00:00
-- url     : https://prove2.me/submissions/100154d5-1fe9-4505-81b9-26a9381edd63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear

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
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
namespace GroundTheory.Heights₂.Heights.NormalModelFibre
theorem _root_.solution : Continuous (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (n := n) (m := M.m)) :=
  continuous_pi fun _ => continuous_apply _
end GroundTheory.Heights₂.Heights.NormalModelFibre
