-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.hermForm_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:12.488957+00:00
-- url     : https://prove2.me/submissions/8997b011-68de-4ce3-8c24-cc8284f9a387

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCC
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_hermForm_eq_mulVec
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} (S : HermForm K k)
    (z : Fin k → Fin k → K) (i : Fin k) (v : Fin k → K) :
    S.h (z i) v = (((rowMat z).map S.c * S.G) *ᵥ v) i := by
  rw [hermForm_eq_mulVec]
  simp [mulVec, dotProduct, Matrix.mul_apply, rowMat]
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
