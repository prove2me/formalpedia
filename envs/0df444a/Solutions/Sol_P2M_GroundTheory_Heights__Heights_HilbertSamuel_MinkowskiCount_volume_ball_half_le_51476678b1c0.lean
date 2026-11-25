-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_volume_ball_half_le_51476678b1c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:55:29.016152+00:00
-- url     : https://prove2.me/submissions/4e4f6852-b0d7-444c-a954-b5c035f4b1d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad

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
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
theorem _root_.solution (La : Submodule ℤ V) [DiscreteTopology La] [IsZLattice ℝ La] (ρ : ℝ) {F : Set V}
    (fund : IsAddFundamentalDomain La F volume) :
    volume (ball (0 : V) (ρ / 2)) ≤
      ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ≥0∞) * volume F := by
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  have : Countable La := inferInstance
  set S := ball (0 : V) (ρ / 2) with hSdef
  set A := {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} with hAdef
  have hS : MeasurableSet S := measurableSet_ball
  have key : ∀ y : V, ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) ≤ (A.ncard : ℝ≥0∞) := by
    intro y
    set T : Set La := {g | (g : V) + y ∈ S} with hTdef
    have h1 : ∑' g : La, S.indicator (1 : V → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, T.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hA : (A.ncard : ℝ≥0∞) = ((A.encard : ℕ∞) : ℝ≥0∞) := by
      rw [← (finite_latticePoints La ρ).cast_ncard_eq]; rfl
    rw [hA]
    refine ENat.toENNReal_le.mpr ?_
    rcases T.eq_empty_or_nonempty with hT | ⟨g₀, hg₀⟩
    · simp [hT]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : V) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hg' : ‖(g : V) + y‖ < ρ / 2 := by simpa [T, S] using hg
      have hg₀' : ‖(g₀ : V) + y‖ < ρ / 2 := by simpa [T, S] using hg₀
      have : (g : V) - g₀ = ((g : V) + y) - ((g₀ : V) + y) := by abel
      show ‖(g : V) - g₀‖ ≤ ρ
      rw [this]
      linarith [norm_sub_le ((g : V) + y) ((g₀ : V) + y)]
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc volume S = ∫⁻ z, S.indicator 1 z := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, (A.ncard : ℝ≥0∞) := lintegral_mono fun z => key z
    _ = A.ncard * volume F := setLIntegral_const _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
