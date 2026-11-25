-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:57.049236+00:00
-- url     : https://prove2.me/submissions/5887865a-ce51-43f2-b77d-9c77e71dd919

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_le_sum_eq_60ecb16347c3

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
theorem _root_.solution (μ : Coord n →₀ ℕ) (d e : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k + e k) :
    ∃ μ₁ μ₂ : Coord n →₀ ℕ, μ = μ₁ + μ₂ ∧ (∀ k, ∑ i, μ₁ ⟨k, i⟩ = d k) ∧ ∀ k, ∑ i, μ₂ ⟨k, i⟩ = e k := by
  classical
  choose g hg hs using fun k ↦
    exists_le_sum_eq (fun i : Fin (n k + 1) ↦ μ ⟨k, i⟩) (d k) (by rw [hμ k]; omega)
  let μ₁ : Coord n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p ↦ g p.1 p.2
  have h₁ : ∀ p, μ₁ p = g p.1 p.2 := fun p ↦ rfl
  refine ⟨μ₁, μ - μ₁, ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · ext p
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, h₁]
    have : g p.1 p.2 ≤ μ p := hg p.1 p.2
    omega
  · simp only [h₁]
    exact hs k
  · have hsplit : ∑ i, μ ⟨k, i⟩ = ∑ i, g k i + ∑ i, (μ - μ₁) ⟨k, i⟩ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Finsupp.tsub_apply, h₁]
      have : g k i ≤ μ ⟨k, i⟩ := hg k i
      omega
    have := hμ k
    have := hs k
    omega
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
