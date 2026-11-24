-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_li_norm_mulVec_apply_le_4c4c2f496192
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:29.039553+00:00
-- url     : https://prove2.me/submissions/d0f064df-0a17-41ee-b15c-6c09de05908c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.HermNorm
theorem _root_.solution (h : HermNorm n) (v : Fin n → ℂ) (l : Fin n) :
    ‖(h.mat *ᵥ v) l‖ ≤ h.norm v := by
  unfold HermNorm.norm
  rw [← Real.sqrt_sq (_root_.norm_nonneg ((h.mat *ᵥ v) l))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖(h.mat *ᵥ v) i‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ l))
end GroundTheory.Heights₂.Heights.HermNorm
