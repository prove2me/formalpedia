-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_H_lineUnique__a92abf7b978f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:46.039468+00:00
-- url     : https://prove2.me/submissions/6d5747e6-5d44-48c2-8477-13db2e01f100

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_IteratedDerivLine
import Theorems.Thm_P2M_Formalism_L2_Th1_H_lineCoeff__fb5a11f6bb6a
import Theorems.Thm_Formalism_L2_Th1_H_LineUnique_of

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
theorem _root_.solution : LineUnique := LineUnique_of lineCoeff'
end Formalism.L2.Th1.H
