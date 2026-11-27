-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_IncidenceNull_hypotheses_inhabited_12b7884d8066
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:12.883092+00:00
-- url     : https://prove2.me/submissions/b9008ab5-c823-4c17-970f-b41f87db45ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace IncidenceNull
theorem _root_.solution :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  isChowForm_point ℚ
end IncidenceNull
end GroundTheory.Heights₂.Heights.Vertical
