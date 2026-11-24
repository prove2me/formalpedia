-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:55.563854+00:00
-- url     : https://prove2.me/submissions/545236cc-5d35-4375-9b79-39941fe37b21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_nonneg_e5b131e01688
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813

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
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : gaussNormOf w (0 : MvPolynomial ι R) = 0 :=
  le_antisymm (gaussNormOf_le w le_rfl fun m => by simp) (gaussNormOf_nonneg w 0)
end GroundTheory.Heights₂.Heights
