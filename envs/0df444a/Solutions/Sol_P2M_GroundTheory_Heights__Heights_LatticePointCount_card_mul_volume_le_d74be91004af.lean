-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePointCount_card_mul_volume_le_d74be91004af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:20.388522+00:00
-- url     : https://prove2.me/submissions/b15b9291-08fa-43a4-9d44-ccc40dde0cf6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq

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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount
namespace GroundTheory.Heights₂.Heights.LatticePointCount
theorem _root_.solution {r : ℕ} (c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) {μ : ℝ}
    (hcov : ∀ y, ∃ l ∈ span ℤ (Set.range c), ‖y - l‖ ≤ μ)
    (X : Finset (EuclideanSpace ℝ (Fin r)))
    (hX : ∀ x ∈ X, x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ 1) :
    (X.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain c) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) := by
  classical
  set L := (span ℤ (Set.range c)).toAddSubgroup with hL
  set F := ZSpan.fundamentalDomain c with hFdef
  have hLc : Countable L := (inferInstance : Countable (span ℤ (Set.range c)))
  have hF : IsAddFundamentalDomain L F volume := ZSpan.isAddFundamentalDomain c volume
  have hball : ∀ g : L, g +ᵥ closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ) =
      closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ) := by
    intro g
    ext v
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [mem_closedBall, dist_eq_norm]
    rw [sub_zero, AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg, neg_add_eq_sub]
  have hpt : ∀ v, (X.card : ℝ≥0∞) ≤
      ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := by
    intro v
    obtain ⟨l, hl, hlv⟩ := hcov v
    let s : Finset L := X.attach.map ⟨fun x => ⟨l + x.1, add_mem hl (hX x.1 x.2).1⟩, fun x y h => by
      apply Subtype.ext
      simpa using congrArg Subtype.val h⟩
    calc (X.card : ℝ≥0∞) = ∑ g ∈ s, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v := by
          rw [Finset.sum_map]
          rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
          · simp
          · intro x _
            rw [Set.indicator_of_mem]
            · rfl
            simp only [mem_closedBall, dist_eq_norm]
            calc ‖v - (l + x.1)‖ = ‖(v - l) - x.1‖ := by rw [sub_add_eq_sub_sub]
              _ ≤ ‖v - l‖ + ‖x.1‖ := norm_sub_le _ _
              _ ≤ μ + 1 := add_le_add hlv (hX x.1 x.2).2
              _ = 1 + μ := add_comm _ _
      _ ≤ ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v :=
          ENNReal.sum_le_tsum s
  calc (X.card : ℝ≥0∞) * volume F = ∫⁻ _ in F, (X.card : ℝ≥0∞) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ v in F, ∑' g : L, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v :=
        lintegral_mono fun v => hpt v
    _ = ∑' g : L, ∫⁻ v in F, (closedBall (g : EuclideanSpace ℝ (Fin r)) (1 + μ)).indicator 1 v :=
        lintegral_tsum fun g => (measurable_one.indicator measurableSet_closedBall).aemeasurable
    _ = ∑' g : L, volume ((g +ᵥ closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) ∩ F) := by
        congr 1
        ext g
        rw [lintegral_indicator_one measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, hball]
    _ = volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) := (hF.measure_eq_tsum _).symm
end GroundTheory.Heights₂.Heights.LatticePointCount
