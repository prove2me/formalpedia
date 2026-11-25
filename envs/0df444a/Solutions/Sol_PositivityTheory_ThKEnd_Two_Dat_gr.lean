-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dat.gr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:15.562223+00:00
-- url     : https://prove2.me/submissions/6c306fc0-9c65-460c-930f-808c9e1863ec

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Dat_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [OpensMeasurableSpace X] [IsProbabilityMeasure lam]
namespace PositivityTheory.ThKEnd.Two
namespace Dat
theorem _root_.solution (h : Dat Γ n a lam l φ c) (hl : ‖l‖ < 1) : Gr a 0 c := fun Ω hΩ => by
  have := h.contc
  obtain ⟨M, hM⟩ := hΩ.exists_bound_of_continuousOn h.contc.continuousOn
  obtain ⟨M', hM'⟩ := hΩ.exists_bound_of_continuousOn (f := fun g => c (a * g) - c g) (Continuous.continuousOn (by fun_prop))
  refine ⟨M + (1 - ‖l‖)⁻¹ * M', fun k κ hκ => ?_⟩
  have e : c (a ^ k * κ) = c κ + (∑ i ∈ Finset.range k, l ^ i) * (c (a * κ) - c κ) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ' a, mul_assoc]; linear_combination ih + h.pow k κ
  have e2 : ‖∑ i ∈ Finset.range k, l ^ i‖ ≤ (1 - ‖l‖)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_pow]
    rw [← tsum_geometric_of_lt_one (norm_nonneg l) hl]
    exact (summable_geometric_of_lt_one (norm_nonneg l) hl).sum_le_tsum _ fun _ _ => by positivity
  rw [pow_zero, mul_one, e]
  refine (norm_add_le _ _).trans (add_le_add (hM κ hκ) ?_)
  rw [norm_mul]
  exact mul_le_mul e2 (hM' κ hκ) (norm_nonneg _) ((norm_nonneg _).trans e2)
end Dat
end PositivityTheory.ThKEnd.Two
