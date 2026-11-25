-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_exists_bound_im_0_a87623faa71f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:34.096048+00:00
-- url     : https://prove2.me/submissions/d88cb019-f4f0-4189-b6a8-d61fd3e8fede

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p ∈ D.K, entrySum ((D.τ0 p.1).map Complex.im) ≤ M := by
  have hcont : ContinuousOn (fun z => entrySum ((D.τ0 z).map Complex.im)) D.U := by
    unfold entrySum
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    simp only [map_apply]
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_im.comp_continuousOn (D.τ0_analytic j k).continuousOn)
  have hKc : IsCompact (Prod.fst '' D.K) := D.isCompact_K.image continuous_fst
  have hsub : Prod.fst '' D.K ⊆ D.U := by
    rintro _ ⟨p, hp, rfl⟩
    exact (D.K_subset hp).1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  have h := hM p.1 ⟨p, hp, rfl⟩
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))
end GroundTheory.Heights₂.Heights.MCBounds
