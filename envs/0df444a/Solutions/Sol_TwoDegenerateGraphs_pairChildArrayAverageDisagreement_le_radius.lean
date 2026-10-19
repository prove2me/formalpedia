-- Prove2me | solution 1 for TwoDegenerateGraphs.pairChildArrayAverageDisagreement_le_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/03db151a-f361-49ef-9723-8788e6c4b474

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_sum_pairCoordinatePairMismatchCount_eq_hammingDist
import Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges :
      ∀ (pair : PairLayer parentCount 1)
        (parent : PairLayer parentCount 0),
        parent ∈ pair.val →
          hammingDist (parents parent) (children pair) ≤ radius) :
    pairChildArrayAverageDisagreement hparents parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ parentCount)
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) ≤
        2 * parentCount.choose 2 * radius := by
    calc
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) =
        ∑ pair : PairLayer parentCount 1,
          ∑ parent ∈ pair.val,
            hammingDist (parents parent) (children pair) :=
        sum_pairCoordinatePairMismatchCount_eq_hammingDist
          parents children
      _ ≤ ∑ pair : PairLayer parentCount 1,
          ∑ _parent ∈ pair.val, radius := by
        apply Finset.sum_le_sum
        intro pair _
        apply Finset.sum_le_sum
        intro parent hparent
        exact hedges pair parent hparent
      _ = ∑ _pair : PairLayer parentCount 1, 2 * radius := by
        apply Finset.sum_congr rfl
        intro pair _
        simp [pair.property]
      _ = 2 * parentCount.choose 2 * radius := by
        simp [pairLayer_card_succ, pairLayer_card_zero,
          Nat.mul_assoc, Nat.mul_comm]
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair : ℕ) : ℝ)) ≤
        2 * (parentCount.choose 2 : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  unfold pairChildArrayAverageDisagreement
  simp_rw [pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    (by omega : 2 ≤ parentCount) parents children]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdimension_real).mpr
  apply (div_le_iff₀ (mul_pos (by norm_num) hpair)).mpr
  nlinarith
end TwoDegenerateGraphs
