-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_continuous_firstPart_81c0042172c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:14.470018+00:00
-- url     : https://prove2.me/submissions/da6d2fbb-4b69-428b-9f45-c6ce0a223a18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly

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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
theorem _root_.solution : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) :=
  continuous_pi fun _ => continuous_apply _
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
