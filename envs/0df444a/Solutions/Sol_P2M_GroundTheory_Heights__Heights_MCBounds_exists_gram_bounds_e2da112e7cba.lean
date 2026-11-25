-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_exists_gram_bounds_e2da112e7cba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:02.948086+00:00
-- url     : https://prove2.me/submissions/5623bf10-15f3-4ba4-975e-05200257b23a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_gram_posDef_179fcbfd6c04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_continuousOn_f_cb26dcfc3511
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_pos_df6c7fe9c329


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
theorem _root_.solution : ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ p ∈ D.K,
    δ ≤ ((D.f p)ᴴ * D.f p).det.re ∧ ((D.f p)ᴴ * D.f p).det.re ≤ M := by
  have hc : ContinuousOn (fun p => ((D.f p)ᴴ * D.f p).det.re) D.K := by
    have h := (continuousOn_f D).mono D.K_subset
    rw [continuousOn_iff_continuous_domRestrict] at h ⊢
    exact Complex.continuous_re.comp (h.matrix_conjTranspose.matrix_mul h).matrix_det
  have hpos : ∀ p ∈ D.K, 0 < ((D.f p)ᴴ * D.f p).det.re := fun p hp =>
    MCDet.re_det_pos (gram_posDef _ (D.f_rank p (D.K_subset hp)))
  rcases D.K.eq_empty_or_nonempty with hK | hK
  · exact ⟨1, 1, one_pos, one_pos, fun p hp => by simp [hK] at hp⟩
  obtain ⟨p0, hp0, hmin⟩ := D.isCompact_K.exists_isMinOn hK hc
  obtain ⟨M, hM⟩ := D.isCompact_K.exists_bound_of_continuousOn hc
  refine ⟨_, max M 1, hpos p0 hp0, by positivity, fun p hp => ⟨hmin hp, ?_⟩⟩
  have h := hM p hp
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))
end GroundTheory.Heights₂.Heights.MCBounds
