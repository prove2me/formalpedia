-- Prove2me | solution 1 for a06_full_history_residual_inline_measurability_46508a87
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:32:26.584771+00:00
-- url     : https://prove2.me/submissions/83a525bf-fc9c-40e4-9135-ed528c652cbe

import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
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
    (hRep : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); (∀ (n : ℕ), ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
        (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
          (fun ω : Ω =>
            (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
              N ω clock = n))))
    (hsum : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; Measurable (fun ω => ∑ i ∈ Finset.range (N ω clock), τ i ω)))
    (hR : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; Measurable R))
    (hF : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; Measurable F))
    (hPos : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; ∀ᵐ ω ∂P, 0 < R ω))
    : (let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1); let R : Ω → ℝ := (fun ω => τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)); let F : Ω → (ℕ → ℝ) := fun ω j => τ (N ω clock + 1 + j) ω; (∀ (u : ℝ) (hu : 0 ≤ u) (B : Set (ℕ → ℝ)) (hB : MeasurableSet B), P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B})) := by
  classical
  dsimp only at hRep hLaw hTail hsum hR hF hPos ⊢
  intro u hu B hB
  let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1)
  have hJoint :=
    AvramDividend.Classical.avram_a06_countwise_iid_residual_future_joint_ae
      τ hτ hiid N hThresholdAE clock hclock hN
      H hH hRep u hu μ hLaw B hB hTail
  have hMarg :=
    AvramDividend.Classical.avram_a06_renewal_residual_future_from_ae_threshold
      τ hτ hiid N hThresholdAE clock hclock hN
      u hu μ hLaw B hB hTail
  calc
    P {ω | ω ∈ H ∧
      u < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-u))) * μ B := hJoint
    _ = P H * P {ω |
      u < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} := by
        rw [mul_assoc, hMarg]
end
