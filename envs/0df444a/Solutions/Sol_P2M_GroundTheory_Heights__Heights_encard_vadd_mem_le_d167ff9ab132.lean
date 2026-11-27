-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_encard_vadd_mem_le_d167ff9ab132
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:33.296376+00:00
-- url     : https://prove2.me/submissions/01a1f37a-7676-46ff-a5fb-7e3457b40b58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module ZSpan NumberField
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]
variable [IsZLattice ℝ L]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [DiscreteTopology L] [IsZLattice ℝ L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : V) :
    {g : L | g +ᵥ x ∈ closedBall (0 : V) (1 / 2)}.encard ≤
      {y : V | y ∈ L ∧ ‖y‖ ≤ 1}.encard := by
  rcases Set.eq_empty_or_nonempty {g : L | g +ᵥ x ∈ closedBall (0 : V) (1 / 2)} with hA | ⟨g₀, hg₀⟩
  · rw [hA, Set.encard_empty]
    exact bot_le
  refine Set.encard_le_encard_of_injOn (f := fun g : L ↦ ((g - g₀ : L) : V)) ?_ ?_
  · intro g hg
    refine ⟨(g - g₀).2, ?_⟩
    simp only [Set.mem_ofPred_eq, mem_closedBall, dist_zero_right, Submodule.vadd_def,
      vadd_eq_add] at hg hg₀
    have : ((g - g₀ : L) : V) = ((g : V) + x) - ((g₀ : V) + x) := by
      rw [Submodule.coe_sub]; abel
    show ‖((g - g₀ : L) : V)‖ ≤ 1
    rw [this]
    calc ‖((g : V) + x) - ((g₀ : V) + x)‖ ≤ ‖(g : V) + x‖ + ‖(g₀ : V) + x‖ := norm_sub_le _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hg hg₀
      _ = 1 := by norm_num
  · intro g _ g' _ hgg'
    have := Subtype.val_injective hgg'
    simpa using this
end GroundTheory.Heights₂.Heights
