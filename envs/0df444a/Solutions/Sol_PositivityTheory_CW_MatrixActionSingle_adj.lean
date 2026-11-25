-- Prove2me | solution 1 for PositivityTheory.CW.MatrixActionSingle.adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:46.198941+00:00
-- url     : https://prove2.me/submissions/357c2ba9-ef92-4d0b-b6e8-c41498a927ff

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_act_apply
import Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_adjSign_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MatrixActionSingle
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.MatrixActionSingle
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Mm E) u) w = inner ℂ u (act (Md ε E) w) := by
  simp only [PiLp.inner_apply, act_apply, Mm, Md, Matrix.of_apply, sum_inner, inner_sum,
    LinearMap.smul_apply, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [adjSign_symm]
  exact hu a b _ _
end PositivityTheory.CW.MatrixActionSingle
