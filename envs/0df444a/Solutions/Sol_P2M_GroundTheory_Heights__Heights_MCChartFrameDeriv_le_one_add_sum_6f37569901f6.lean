-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCChartFrameDeriv_le_one_add_sum_6f37569901f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:40.142458+00:00
-- url     : https://prove2.me/submissions/76a84a30-8cf7-4d2f-8014-d01cf3805fe2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartFrameDeriv

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
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartFrameDeriv
namespace GroundTheory.Heights₂.Heights.MCChartFrameDeriv
theorem _root_.solution {g r : ℕ} (A : Fin g → Fin r → ℝ) (hA : ∀ j l, 0 < A j l) (j : Fin g)
    (l : Fin r) : A j l ≤ 1 + ∑ j', ∑ l', A j' l' := by
  have h1 : A j l ≤ ∑ l', A j l' :=
    Finset.single_le_sum (f := fun l' => A j l') (fun l' _ => (hA j l').le) (Finset.mem_univ l)
  have h2 : ∑ l', A j l' ≤ ∑ j', ∑ l', A j' l' :=
    Finset.single_le_sum (f := fun j' => ∑ l', A j' l')
      (fun j' _ => Finset.sum_nonneg fun l' _ => (hA j' l').le) (Finset.mem_univ j)
  linarith
end GroundTheory.Heights₂.Heights.MCChartFrameDeriv
