-- Prove2me | solution 1 for SoficGroups.weighted_midrank_dominant_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/861078ea-01dd-44c0-81ce-ecfc84b1b6b0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_midrankVariance_controls_dominant_mass

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*}
    (I : Finset ι) (weight : ι → ℝ)
    (q : ι → List ℝ) (m : ι → ℝ)
    (hweight : ∀ i ∈ I, 0 ≤ weight i)
    (hsum : ∀ i ∈ I, (q i).sum = 1)
    (hpositive : ∀ i ∈ I, ∀ x ∈ q i, 0 ≤ x)
    (hdominant : ∀ i ∈ I, ∀ x ∈ q i, x ≤ m i) :
    (∑ i ∈ I, weight i * (1 - m i)) ≤
      12 * ∑ i ∈ I, weight i * midrankVariance (q i) := by
  calc
    (∑ i ∈ I, weight i * (1 - m i)) ≤
        ∑ i ∈ I, 12 * (weight i * midrankVariance (q i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hvar := midrankVariance_controls_dominant_mass
        (q i) (m i) (hsum i hi) (hpositive i hi) (hdominant i hi)
      have hpoint : 1 - m i ≤ 12 * midrankVariance (q i) := by
        linarith
      calc
        weight i * (1 - m i) ≤
            weight i * (12 * midrankVariance (q i)) :=
          mul_le_mul_of_nonneg_left hpoint (hweight i hi)
        _ = 12 * (weight i * midrankVariance (q i)) := by ring
    _ = 12 * ∑ i ∈ I, weight i * midrankVariance (q i) := by
      rw [Finset.mul_sum]
end SoficGroups
