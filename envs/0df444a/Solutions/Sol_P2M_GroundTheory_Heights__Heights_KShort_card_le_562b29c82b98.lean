-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_card_le_562b29c82b98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:18.656427+00:00
-- url     : https://prove2.me/submissions/401f4a2b-eef4-4e91-bedf-d3196c95e7c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
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
theorem _root_.solution (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {lam r : ℝ} (hlam : 0 < lam) (hr : lam ≤ r)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (({v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r}.ncard : ℕ) : ℝ) ≤ (3 * r / lam) ^ finrank ℝ U := by
  classical
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  set μ : Measure U := (Module.finBasis ℝ U).addHaar with hμ
  set a := finrank ℝ U with ha
  set T : Set U := {w | (w : EuclideanSpace ℝ (Fin n)) ∈ L ∧ ‖w‖ ≤ r} with hT
  have hTfin : T.Finite :=
    ((finite_ball L r).preimage Subtype.val_injective.injOn).subset fun w hw => ⟨hw.1, hw.2⟩
  have himage : Subtype.val '' T = {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1, w.2, hw.2⟩
    · rintro ⟨hL, hU, hr'⟩
      exact ⟨⟨v, hU⟩, ⟨hL, hr'⟩, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_eq_toFinset_card T hTfin]
  set s := hTfin.toFinset with hs
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set U) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    have hw1 : (w : EuclideanSpace ℝ (Fin n)) ∈ L := by
      simpa [hs, hT] using (Set.Finite.mem_toFinset hTfin).1 hw |>.1
    have hw2 : (w' : EuclideanSpace ℝ (Fin n)) ∈ L := by
      simpa [hs, hT] using (Set.Finite.mem_toFinset hTfin).1 hw' |>.1
    have hsub : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ∈ L := by
      rw [Submodule.coe_sub]; exact L.sub_mem hw1 hw2
    have hne0 : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      apply hne
      have : w - w' = 0 := Subtype.ext h
      exact sub_eq_zero.1 this
    have := hmin _ hsub hne0
    simpa using this
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : U) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    have hwr : ‖w‖ ≤ r := ((Set.Finite.mem_toFinset hTfin).1 hw).2
    rw [mem_ball_zero_iff]
    rw [mem_ball] at hxw
    calc ‖x‖ ≤ ‖w‖ + dist x w := by
          rw [dist_eq_norm]
          calc ‖x‖ = ‖w + (x - w)‖ := by abel_nf
            _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ a := by positivity
  have hcard : (s.card : ℝ) ≤ ((r + lam / 2) / (lam / 2)) ^ a := by
    rw [div_pow, le_div_iff₀ hpos]; exact hle'
  refine hcard.trans (pow_le_pow_left₀ (div_nonneg (by linarith) hl2.le) ?_ a)
  rw [div_le_div_iff₀ hl2 hlam]
  nlinarith
end GroundTheory.Heights₂.Heights.KShort
