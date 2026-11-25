-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PivotProductBound_prod_range_pivot_67280104cdf8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:24.697279+00:00
-- url     : https://prove2.me/submissions/df2789ec-a46d-4f8e-a2a6-ea1a511be320

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotProductBound

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.PivotProductBound
namespace GroundTheory.Heights₂.Heights.PivotProductBound
theorem _root_.solution (hLB : LeadMinorBasic.Statement) {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) : ∀ r, r ≤ d → ∏ i ∈ Finset.range r, pivot S i = leadMinor S r := by
  intro r
  induction r with
  | zero => intro _; simp [(hLB d S).1]
  | succ n ih =>
    intro hn
    rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hn), pivot,
      mul_div_cancel₀ _ ((hLB d S).2.2 hS n (Nat.le_of_succ_le hn)).ne']
end GroundTheory.Heights₂.Heights.PivotProductBound
