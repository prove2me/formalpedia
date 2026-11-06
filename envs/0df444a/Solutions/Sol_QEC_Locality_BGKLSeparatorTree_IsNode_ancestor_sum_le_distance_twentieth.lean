-- Prove2me | solution 1 for QEC.Locality.BGKLSeparatorTree.IsNode.ancestor_sum_le_distance_twentieth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:27:09.788993+00:00
-- url     : https://prove2.me/submissions/c07abf44-1136-42af-aa44-06f74e6c2e4e

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_bgklDecayRatio_lt_one
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_ancestor_sum_add_potential_le
import Theorems.Thm_QEC_Locality_bgklSmallBoundaryEpsilon_pos

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
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹) :
    (ancestorSeparatorCardSum ancestors : ℝ) ≤ (d : ℝ) / 20 := by
  have hbeta : 1 ≤ beta := hProfile.1
  have hexponentPos : 0 < exponent := hProfile.2.1
  have hepsilon := bgklSmallBoundaryEpsilon_pos hbeta hexponentPos
  have hrootPower : Real.rpow root.card exponent ≤
      bgklSmallBoundaryEpsilon beta exponent * d := by
    exact (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg root.card)
      (mul_nonneg hepsilon.le (Nat.cast_nonneg d)) hexponentPos).mp hSmall
  have hpotential := hnode.ancestor_sum_add_potential_le hd hProfile
  have hcoefficient : 0 ≤ beta / (1 - bgklDecayRatio exponent) := by
    exact div_nonneg (zero_le_one.trans hbeta)
      (sub_nonneg.mpr (bgklDecayRatio_lt_one hexponentPos).le)
  have hrootScaled := mul_le_mul_of_nonneg_left hrootPower hcoefficient
  have hresidual : 0 ≤ beta / (1 - bgklDecayRatio exponent) *
      Real.rpow node.card exponent :=
    mul_nonneg hcoefficient (Real.rpow_nonneg (Nat.cast_nonneg node.card) _)
  have hconstant : beta / (1 - bgklDecayRatio exponent) *
      (bgklSmallBoundaryEpsilon beta exponent * (d : ℝ)) = (d : ℝ) / 20 := by
    rw [bgklSmallBoundaryEpsilon]
    have hbeta0 : beta ≠ 0 := ne_of_gt (zero_lt_one.trans_le hbeta)
    have hden0 : 1 - bgklDecayRatio exponent ≠ 0 :=
      ne_of_gt (sub_pos.mpr (bgklDecayRatio_lt_one hexponentPos))
    field_simp
  rw [hconstant] at hrootScaled
  linarith
end BGKLSeparatorTree.IsNode
end QEC.Locality
