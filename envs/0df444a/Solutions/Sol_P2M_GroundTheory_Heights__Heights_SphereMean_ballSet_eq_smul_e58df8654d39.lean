-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_eq_smul_e58df8654d39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:40.359486+00:00
-- url     : https://prove2.me/submissions/d4b5e5e9-f172-4cf3-987f-b6b3376b2267

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_smul_0f1c388bb826

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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution {n : ℕ} {s : ℝ} (hs : 0 < s) : ballSet n s = √s • ballSet n 1 := by
  have h : 0 < √s := Real.sqrt_pos.mpr hs
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ h.ne']
  simp only [ballSet, mem_ofPred_eq, sqNorm_smul, inv_pow, Real.sq_sqrt hs.le]
  rw [inv_mul_lt_iff₀ hs, mul_one]
end GroundTheory.Heights₂.Heights.SphereMean
