-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_omega_sq_sevenQ_2845b5ee752b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:43:34.61804+00:00
-- url     : https://prove2.me/submissions/de6721e1-acc1-4812-abd4-08437e67da32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution : (⟨0, 1⟩ : QuadraticFieldSqrtNegSeven) ^ 2 = -((7 : ℕ) : QuadraticFieldSqrtNegSeven) := by
  ext <;> simp [sq, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
end GroundTheory.Heights₂.Theta
