-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.chainComplex_cocycle_weight_ge_of_locallyMinimal_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:03.378139+00:00
-- url     : https://prove2.me/submissions/b72adbbe-7a05-47c0-a1e1-33d323a40460

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_weight_ge_of_locallyMinimal_cycle_bound
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat) (lowerBound : Nat)
    (hlocal : ∀ c : Word F ι, c ∈ K.middleCocycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryCoboundaryMoves K) c →
        lowerBound ≤ weight c)
    (c : Word F ι) (hcZ : c ∈ K.middleCocycleCode.carrier)
    (hcB : c ∉ K.firstCoboundaryCheckCode.carrier) :
    lowerBound ≤ weight c := by
  exact weight_ge_of_locallyMinimal_cycle_bound weight
    K.middleCocycleCode.carrier.toAddSubgroup
    K.firstCoboundaryCheckCode.carrier.toAddSubgroup
    (elementaryCoboundaryMoves K)
    K.firstCoboundaryCheckCode_le_middleCocycleCode
    (elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode K)
    lowerBound hlocal c hcZ hcB
end QEC.Coding.LocallyMinimalDistance
