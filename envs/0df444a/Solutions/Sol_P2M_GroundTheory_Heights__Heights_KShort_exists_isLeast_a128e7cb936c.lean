-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_exists_isLeast_a128e7cb936c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:38.231519+00:00
-- url     : https://prove2.me/submissions/d6028134-bb93-43de-a963-afe84c5975b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_exists_ne_zero_1ce62324bc5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe

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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ lam : ℝ, 0 < lam ∧ IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ t = ‖v‖} lam := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero hn L
  have hfin : {v | v ∈ L ∧ ‖v‖ ≤ ‖v₀‖ ∧ v ≠ 0}.Finite :=
    (finite_ball L ‖v₀‖).subset fun v hv => ⟨hv.1, hv.2.1⟩
  have hne : hfin.toFinset.Nonempty := ⟨v₀, by simp [hv₀, hv₀0]⟩
  obtain ⟨w, hw, hwmin⟩ := hfin.toFinset.exists_min_image (fun v => ‖v‖) hne
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw hwmin
  refine ⟨‖w‖, norm_pos_iff.2 hw.2.2, ⟨w, hw.1, hw.2.2, rfl⟩, ?_⟩
  rintro t ⟨v, hv, hv0, rfl⟩
  by_cases h : ‖v‖ ≤ ‖v₀‖
  · exact hwmin v ⟨hv, h, hv0⟩
  · push Not at h
    linarith [hw.2.1]
end GroundTheory.Heights₂.Heights.KShort
