-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIncDomain_isHomogeneous_linForm_5e6e05fede50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:46.890796+00:00
-- url     : https://prove2.me/submissions/133f54ec-24c2-4505-b731-eed0fee8e173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncDomain
namespace GroundTheory.Heights₂.Heights.ChartIncDomain
theorem _root_.solution {F : Type*} [CommRing F] {n : ℕ} (t : Fin n → F) :
    (linForm t).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X _ _).C_mul _
end GroundTheory.Heights₂.Heights.ChartIncDomain
