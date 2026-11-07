-- Prove2me | solution 1 for QEC.Coding.mem_trivial_of_weight_lt_of_add_weight_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:47.953829+00:00
-- url     : https://prove2.me/submissions/c1739021-c858-41cb-9ae3-61196acd09c7

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F]
  [DecidableEq F] [Fintype ι]
namespace QEC.Coding
theorem _root_.solution
    (ambient trivial : LinearCode F ι)
    (hsub : trivial.carrier ≤ ambient.carrier) (threshold : Nat)
    (hreduce : ∀ x : Word F ι, x ∈ ambient.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ y : Word F ι, y ∈ trivial.carrier ∧
        HammingWeight (x + y) < HammingWeight x)
    (x : Word F ι) (hx : x ∈ ambient.carrier)
    (hweight : HammingWeight x < threshold) : x ∈ trivial.carrier := by
  have descend : ∀ n : Nat, ∀ z : Word F ι,
      HammingWeight z = n → z ∈ ambient.carrier →
      HammingWeight z < threshold → z ∈ trivial.carrier := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hn hz hlt
      by_cases hzero : z = 0
      · subst z
        exact trivial.carrier.zero_mem
      obtain ⟨y, hy, hdecrease⟩ := hreduce z hz hzero hlt
      have hsmall : HammingWeight (z + y) < n := by
        simpa only [hn] using hdecrease
      have hsum : z + y ∈ trivial.carrier :=
        ih (HammingWeight (z + y)) hsmall (z + y) rfl
          (ambient.carrier.add_mem hz (hsub hy)) (hdecrease.trans hlt)
      have hdiff := trivial.carrier.sub_mem hsum hy
      simpa only [add_sub_cancel_right] using hdiff
  exact descend (HammingWeight x) x rfl hx hweight
end QEC.Coding
