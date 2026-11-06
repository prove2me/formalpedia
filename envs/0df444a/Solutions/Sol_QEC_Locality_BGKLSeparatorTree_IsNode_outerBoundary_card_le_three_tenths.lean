-- Prove2me | solution 1 for QEC.Locality.BGKLSeparatorTree.IsNode.outerBoundary_card_le_three_tenths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:29:15.429537+00:00
-- url     : https://prove2.me/submissions/c278a066-2a17-4c1b-adae-2b52cf9b0346

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_outerBoundary_subset
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_ancestor_sum_le_distance_twentieth
import Theorems.Thm_QEC_Locality_ancestorSeparatorUnion_card_le_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
namespace BGKLSeparatorTree.IsNode
theorem _root_.solution
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hRootBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d) :
    ((fixedGeneratorOuterBoundaryFinset P node).card : ℝ) ≤ 3 * (d : ℝ) / 10 := by
  have hsubset := hnode.outerBoundary_subset
  have hnodeCard : (fixedGeneratorOuterBoundaryFinset P node).card ≤
      (fixedGeneratorOuterBoundaryFinset P root).card +
        (ancestorSeparatorUnion ancestors).card := by
    exact (Finset.card_le_card hsubset).trans
      (Finset.card_union_le _ _)
  have hancestorUnion : (ancestorSeparatorUnion ancestors).card ≤
      ancestorSeparatorCardSum ancestors := ancestorSeparatorUnion_card_le_sum ancestors
  have hancestor := hnode.ancestor_sum_le_distance_twentieth
    hd hProfile hSmall
  have hrootBoundaryReal :
      ((fixedGeneratorOuterBoundaryFinset P root).card : ℝ) ≤ (d : ℝ) / 4 := by
    have hcast : (4 : ℝ) * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d := by
      exact_mod_cast hRootBoundary
    linarith
  have hnodeCardReal : ((fixedGeneratorOuterBoundaryFinset P node).card : ℝ) ≤
      ((fixedGeneratorOuterBoundaryFinset P root).card : ℝ) +
        (ancestorSeparatorCardSum ancestors : ℝ) := by
    exact_mod_cast hnodeCard.trans (Nat.add_le_add_left hancestorUnion _)
  linarith
end BGKLSeparatorTree.IsNode
end QEC.Locality
