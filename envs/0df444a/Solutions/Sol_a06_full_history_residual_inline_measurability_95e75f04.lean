-- Prove2me | solution 1 for a06_full_history_residual_inline_measurability_95e75f04
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:36:33.799427+00:00
-- url     : https://prove2.me/submissions/3309f91c-14f0-4438-bccd-8c4f5017cf04

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_history_comap_prefix_representation
import Theorems.Thm_AvramDividend_Classical_chat06_prefix_observed_count_history_measurable
import Theorems.Thm_AvramDividend_Classical_chat06_arrival_prefix_reconstructs_past_count
import Theorems.Thm_AvramDividend_Classical_avram_a06_countwise_iid_residual_future_joint_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_renewal_residual_future_from_ae_threshold
import Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_residual_wait_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_index_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_full_joint_factor_of_positive_tail_rectangles
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (H : Set Ω) (hH : MeasurableSet H)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (D : Set (ℝ × (ℕ → ℝ))) (hD : MeasurableSet D) 
    (hLaw : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ), HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)))
    (hTail : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ) (u : ℝ) (hu : 0 ≤ u), P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))))
    : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ), ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
        (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
          (fun ω : Ω =>
            (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
              N ω clock = n))) := by
  classical
  dsimp only
  intro n
  let Z : Ω → (ℕ → ℝ) :=
    fun ω i => if i < n then τ i ω else 0
  let path : Ω → (Set.Iic clock → ℕ) :=
    fun ω s => N ω (s : ℝ)
  let φ : (ℕ → ℝ) → (Set.Iic clock → ℕ) :=
    fun z s => ((Finset.range n).filter
      (fun k => (∑ i ∈ Finset.range (k + 1), z i) ≤ (s : ℝ))).card
  have hφ : Measurable φ := by
    exact AvramDividend.Classical.chat06_prefix_observed_count_history_measurable n clock
  have hPath : ∀ᵐ ω ∂P, N ω clock = n → path ω = φ (Z ω) := by
    filter_upwards [hThresholdAE] with ω hThreshold
    intro hn
    funext s
    have hReconstruct :=
      AvramDividend.Classical.chat06_arrival_prefix_reconstructs_past_count
        (fun i => τ i ω) (Z ω) (N ω) clock (s : ℝ)
        s.property n hn hThreshold (by intro i; rfl)
    exact hReconstruct.symm
  exact AvramDividend.Classical.chat06_history_comap_prefix_representation
    P (fun ω => N ω clock) n Z path φ hφ hPath H hHpast
end
