-- Prove2me | solution 1 for PositivityTheory.KReal.formT_positionA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:27.748308+00:00
-- url     : https://prove2.me/submissions/e288e4f7-726c-42c6-a0c9-7a92a2033d78

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasC
import Theorems.Thm_PositivityTheory_KReal_sum_upd

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
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.KReal
theorem _root_.solution (m : Matrix I I ℂ) (Θ Θ' : (J → I) → V) :
    formT (positionA mᴴ Θ) Θ' = formT Θ (positionA m Θ') := by
  unfold PositivityTheory.KReal.formT PositivityTheory.KReal.positionA
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    starRingEnd_apply, star_star]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  conv_rhs => rw [PositivityTheory.KReal.sum_upd s]
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
end PositivityTheory.KReal
