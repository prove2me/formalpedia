-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartImagContinuous_proof_b3d17a2a41f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:03.019172+00:00
-- url     : https://prove2.me/submissions/df3ca993-93ef-4ece-8abf-eabd9117c4f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagContinuous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cuspTime_continuousOn_ff6645c3856f

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
namespace GroundTheory.Heights₂.Heights
namespace ChartImagContinuous
theorem _root_.solution : ChartImagContinuous.Statement := by
  intro D
  have hsub : D.Ustar ⊆ D.U := fun z hz => hz.1
  have hτ : ∀ k l, ContinuousOn (fun z => (D.τ0 z k l).im) D.Ustar := fun k l =>
    Complex.continuous_im.comp_continuousOn ((D.τ0_analytic k l).continuousOn.mono hsub)
  have ht : ∀ j, ContinuousOn (fun z => cuspTime D.a_le z j) D.Ustar := fun j =>
    cuspTime_continuousOn D.a_le D.U j
  show ContinuousOn (fun z => chartImag D.a_le D.τ0 D.B z) D.Ustar
  refine continuousOn_pi.mpr fun k => continuousOn_pi.mpr fun l => ?_
  simp only [chartImag, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  exact (hτ k l).add (continuousOn_finsetSum _ fun j _ => (ht j).mul continuousOn_const)
end ChartImagContinuous
end GroundTheory.Heights₂.Heights
