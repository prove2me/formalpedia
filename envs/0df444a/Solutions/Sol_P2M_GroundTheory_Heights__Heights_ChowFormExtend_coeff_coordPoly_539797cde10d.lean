-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_coeff_coordPoly_539797cde10d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:42.010803+00:00
-- url     : https://prove2.me/submissions/a7fac792-09fb-4a90-96b7-3e92bbeaa2ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend

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
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (φ : L →ₗ[K] K) (p : MvPolynomial Y L) (m : Y →₀ ℕ) :
    coeff m (coordPoly φ p) = φ (coeff m p) :=
  rfl
end GroundTheory.Heights₂.Heights.ChowFormExtend
