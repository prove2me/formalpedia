-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLowerBlockBound_entry_bound_a0f56bc4d3ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:35.61911+00:00
-- url     : https://prove2.me/submissions/10a68cd4-59d2-4571-98c4-65a6f1cb86fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartLowerHeightsound

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
open GroundTheory.Heights₂.Heights.ChartLowerBlockBound
namespace GroundTheory.Heights₂.Heights.ChartLowerBlockBound
theorem _root_.solution (D : PeriodChartData) (i l : Fin D.g) :
    ∃ C : ℝ, ∀ p ∈ D.K, ‖D.τ0 p.1 i l‖ ≤ C := by
  have hc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  have hcont : ContinuousOn (fun z => D.τ0 z i l) (Prod.fst '' D.K) :=
    ((D.τ0_analytic i l).continuousOn).mono hsub
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  exact ⟨C, fun p hp => hC p.1 ⟨p, hp, rfl⟩⟩
end GroundTheory.Heights₂.Heights.ChartLowerBlockBound
