-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelFibre_isClosed_zeroSetIn_e835e0b1dee8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:09.553361+00:00
-- url     : https://prove2.me/submissions/d317052e-a6c0-488c-9fe2-d614dd208834

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
theorem _root_.solution : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) := by
  have h : IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal = ⋂ f ∈ M.ideal, {z | eval z f = 0} := by
    ext z
    simp [IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn]
  rw [h]
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
end GroundTheory.Heights₂.Heights.NormalModelFibre
