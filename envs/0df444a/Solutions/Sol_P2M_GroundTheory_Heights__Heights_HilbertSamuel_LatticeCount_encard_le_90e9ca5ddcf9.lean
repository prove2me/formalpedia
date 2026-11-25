-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_encard_le_90e9ca5ddcf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:59.315443+00:00
-- url     : https://prove2.me/submissions/733212c1-5059-4e80-a072-a0885b2d6382

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PLatticeCount
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LatticeCount_exists_near_91c44c1fd18c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Metric Module ZSpan
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace LatticeCount
theorem _root_.solution (B : ShortLatticeBasis La c) (b : ℝ) (x : V) :
    {y : V | y ∈ La ∧ ‖y‖ ≤ b}.encard ≤
      {g : La | g +ᵥ x ∈ closedBall (0 : V) (b + finrank ℝ V * c)}.encard := by
  classical
  obtain ⟨μ, hμ, hxμ⟩ := LatticeCount.exists_near La B x
  refine Set.encard_le_encard_of_injOn
    (f := fun y : V ↦ if h : y ∈ La then (⟨y + μ, La.add_mem h hμ⟩ : La) else 0) ?_ ?_
  · rintro y ⟨hy, hyb⟩
    simp only [Set.mem_ofPred_eq, hy, dif_pos, mem_closedBall, dist_zero_right,
      Submodule.vadd_def, vadd_eq_add]
    calc ‖y + μ + x‖ = ‖y + (x + μ)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖x + μ‖ := norm_add_le _ _
      _ ≤ b + finrank ℝ V * c := add_le_add hyb hxμ
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ h
    simp only [hy, hy', dif_pos, Subtype.mk.injEq, add_left_inj] at h
    exact h
end LatticeCount
end GroundTheory.Heights₂.Heights.HilbertSamuel
