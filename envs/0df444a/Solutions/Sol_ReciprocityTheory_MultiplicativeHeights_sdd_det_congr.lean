-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_det_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:44.524998+00:00
-- url     : https://prove2.me/submissions/4fac8f3e-ed41-4a07-81fb-d1f3110583d6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_norm_det_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (B D : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ * D * B).det = ((‖B.det‖ ^ 2 : ℝ) : ℂ) * D.det := by
  rw [det_mul, det_mul, ← sdd_norm_det_sq B, det_mul]
  ring
end ReciprocityTheory.MultiplicativeHeights
