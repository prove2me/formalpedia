-- Prove2me | solution 1 for PositivityTheory.KReal.matOp_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:14.764582+00:00
-- url     : https://prove2.me/submissions/ef484087-3f67-429e-9f53-42019e987b13

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
import Theorems.Thm_PositivityTheory_KReal_matOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution (m : Matrix I I ℂ) (x y : PiLp 2 (fun _ : I => V)) :
    ⟪matOp m x, y⟫_ℂ = ⟪x, matOp mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, matOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl
end PositivityTheory.KReal
