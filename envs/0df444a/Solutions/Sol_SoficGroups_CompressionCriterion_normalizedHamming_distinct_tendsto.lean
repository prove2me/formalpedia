-- Prove2me | solution 1 for SoficGroups.CompressionCriterion.normalizedHamming_distinct_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/18b6b63a-3122-4967-a0bb-9d046a47f678

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_le_one
import Theorems.Thm_SoficGroups_normalizedHamming_mul_right

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
open SoficGroups.CompressionCriterion
open Filter Topology
namespace SoficGroups.CompressionCriterion
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    {g h : G} (hne : g ≠ h) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action g) ((A.model n).action h))
      atTop (𝓝 1) := by
  have hdifference : g * h⁻¹ ≠ 1 := by
    intro he
    apply hne
    have := congrArg (fun x : G => x * h) he
    simpa using this
  have hseparation := A.separated (g * h⁻¹) hdifference
  have hmultiplication := A.multiplicative (g * h⁻¹) h
  have hlower (n : ℕ) :
      SoficGroups.normalizedHamming
        ((A.model n).action (g * h⁻¹)) 1 -
          SoficGroups.normalizedHamming
            ((A.model n).action ((g * h⁻¹) * h))
            ((A.model n).action (g * h⁻¹) *
              (A.model n).action h) ≤
        SoficGroups.normalizedHamming
          ((A.model n).action g) ((A.model n).action h) := by
    have htriangle := SoficGroups.normalizedHamming_triangle
      ((A.model n).action (g * h⁻¹) * (A.model n).action h)
      ((A.model n).action g)
      ((A.model n).action h)
    have hright := SoficGroups.normalizedHamming_mul_right
      ((A.model n).action h) ((A.model n).action (g * h⁻¹)) 1
    have hsym := SoficGroups.normalizedHamming_comm
      ((A.model n).action g)
      ((A.model n).action (g * h⁻¹) * (A.model n).action h)
    have hword : (g * h⁻¹) * h = g := by simp
    rw [hword] at *
    simp only [one_mul] at hright
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action (g * h⁻¹)) 1 -
          SoficGroups.normalizedHamming
            ((A.model n).action ((g * h⁻¹) * h))
            ((A.model n).action (g * h⁻¹) * (A.model n).action h))
      atTop (𝓝 1) by
        simpa using hseparation.sub hmultiplication)
    tendsto_const_nhds
  · exact hlower
  · intro n
    exact SoficGroups.normalizedHamming_le_one _ _
end SoficGroups.CompressionCriterion
