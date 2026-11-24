-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_finrank_sevenQ_3d28983f8fd9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:59.040442+00:00
-- url     : https://prove2.me/submissions/dccff6b6-50ea-4a2e-b6f6-2c7c76169d1e

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
theorem _root_.solution : Module.finrank ℚ QuadraticFieldSqrtNegSeven = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _
end GroundTheory.Heights₂.Theta
