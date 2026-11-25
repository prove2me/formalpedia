-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_one_block_72430939ba75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:16.894837+00:00
-- url     : https://prove2.me/submissions/f47948ba-fec2-4597-90dd-d2335c2c13d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock

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
theorem _root_.solution {Ω : Type} [Field Ω] (m : ℕ) (x' : Fin (m + 1) → Ω) :
    monomialValues (n := fun _ : Unit ↦ m) (fun p ↦ x' p.2) (fun _ ↦ 1) = Set.range x' := by
  classical
  ext s
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have hsum : ∑ i, μ ⟨(), i⟩ = 1 := hμ ()
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hsum
    have hj1 : μ ⟨(), j⟩ = 1 := by omega
    have hrest := Finset.sum_eq_zero_iff.mp (by omega : ∑ i ∈ Finset.univ.erase j, μ ⟨(), i⟩ = 0)
    refine ⟨j, ?_⟩
    rw [Fintype.prod_eq_single (⟨(), j⟩ : Coord fun _ : Unit ↦ m)]
    · simp [hj1]
    · rintro ⟨⟨⟩, i⟩ hi
      have hij : i ≠ j := fun h ↦ hi (h ▸ rfl)
      rw [hrest i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩), pow_zero]
  · rintro ⟨j, rfl⟩
    refine ⟨Finsupp.single ⟨(), j⟩ 1, fun k ↦ ?_, ?_⟩
    · simp [Finsupp.single_apply]
    · rw [← Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_single_index (by simp)]
      simp
end GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
