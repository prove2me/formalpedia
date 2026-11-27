-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFrameDeriv_proof_c781661695db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:41.190584+00:00
-- url     : https://prove2.me/submissions/6875b20e-6063-4634-98d9-5cb333c238a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartFrameDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCChartFrameDeriv_le_one_add_sum_6f37569901f6

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
open MCChartFrameDeriv
namespace GroundTheory.Heights₂.Heights
namespace ChartFrameDeriv
theorem _root_.solution (h₁ : AnalyticDerivBound.Statement) : ChartFrameDeriv.Statement := by
  intro D
  have hU : IsOpen (D.U ×ˢ D.V) := D.isOpen_U.prod D.isOpen_V
  have hex : ∀ j l, ∃ A : ℝ, 0 < A ∧ ∀ x ∈ D.K,
      DifferentiableAt ℝ (fun q => D.f q j l) x ∧ ‖D.f x j l‖ ≤ A ∧
        ‖fderiv ℝ (fun q => D.f q j l) x‖ ≤ A := fun j l =>
    h₁ (fun q => D.f q j l) (D.U ×ˢ D.V) D.K hU (D.f_analytic j l) D.isCompact_K D.K_subset
  choose A hApos hA using hex
  have hsum : 0 ≤ ∑ j, ∑ l, A j l :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hApos j l).le
  refine ⟨1 + ∑ j, ∑ l, A j l, by linarith, fun p hp j l => ?_⟩
  obtain ⟨hd, hb, hb'⟩ := hA j l p hp
  have hle := le_one_add_sum A hApos j l
  exact ⟨hd, hb.trans hle, hb'.trans hle⟩
end ChartFrameDeriv
end GroundTheory.Heights₂.Heights
