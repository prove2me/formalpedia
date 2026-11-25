-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussLemma_c45298130ae9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:46.023803+00:00
-- url     : https://prove2.me/submissions/a42b8b8c-fe3a-49f1-a79d-69be7c5fd5c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_mul_e42d0b485d41

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
open MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : GaussLemma.Statement := fun _K _ _ v _ι f g => gaussNorm_mul v f g
end GroundTheory.Heights₂.Heights
