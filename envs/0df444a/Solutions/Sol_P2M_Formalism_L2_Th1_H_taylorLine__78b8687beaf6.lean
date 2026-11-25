-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_H_taylorLine__78b8687beaf6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:47.046802+00:00
-- url     : https://prove2.me/submissions/98e61846-ea92-4cf6-894d-b6aa78d51da7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_P2M_Formalism_L2_Th1_H_lineCoeff__fb5a11f6bb6a
import Theorems.Thm_Formalism_L2_Th1_H_TaylorLine_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : TaylorLine := TaylorLine_of lineCoeff'
end Formalism.L2.Th1.H
