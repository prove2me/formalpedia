-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjNullstellensatz_hypotheses_inhabited_a6fca8640d3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:57.776358+00:00
-- url     : https://prove2.me/submissions/88085f29-9a21-4360-98a4-e735e849b619

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300


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
namespace GroundTheory.Heights₂.Heights
namespace ProjNullstellensatz
theorem _root_.solution : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  isProjPrime_point ℚ
end ProjNullstellensatz
end GroundTheory.Heights₂.Heights
