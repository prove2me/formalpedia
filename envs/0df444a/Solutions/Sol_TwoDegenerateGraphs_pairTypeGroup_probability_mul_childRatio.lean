-- Prove2me | solution 1 for TwoDegenerateGraphs.pairTypeGroup_probability_mul_childRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/074c8d54-254f-47c7-b42a-0818de75a76a

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
        ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroupChildOnes parents children
        coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  by_cases hgroup : (pairTypeGroup parents coordinate bitType).card = 0
  · have hchild :
        (pairTypeGroupChildOnes parents children
          coordinate bitType).card = 0 := by
      have hle := pairTypeGroupChildOnes_card_le
        parents children coordinate bitType
      omega
    simp [hgroup, hchild]
  · have hgroup_real :
        ((pairTypeGroup parents coordinate bitType).card : ℝ) ≠ 0 := by
      exact_mod_cast hgroup
    field_simp [hpair.ne', hgroup_real]
end TwoDegenerateGraphs
