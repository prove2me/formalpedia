-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:44.978338+00:00
-- url     : https://prove2.me/submissions/b468519c-96ae-470c-b9bc-40a52d778864

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice

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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < sqNorm x := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : 0 < ‖x j‖ ^ 2 := by positivity
  linarith
end GroundTheory.Heights₂.Heights.SphereMean
