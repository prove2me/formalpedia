-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_continuous_pointOf_0847939ca07e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:03.942148+00:00
-- url     : https://prove2.me/submissions/69c3f808-4082-4c0d-be4b-24a8a1c6c70e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) : Continuous h.pointOf := by
  unfold HermNorm.pointOf
  exact Continuous.matrix_mulVec continuous_const (continuous_pi fun i => by fun_prop)
end HermNorm
end GroundTheory.Heights₂.Heights
