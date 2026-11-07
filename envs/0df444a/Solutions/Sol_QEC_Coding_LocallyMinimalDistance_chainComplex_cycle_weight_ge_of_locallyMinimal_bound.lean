-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.chainComplex_cycle_weight_ge_of_locallyMinimal_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:02.422617+00:00
-- url     : https://prove2.me/submissions/dd207ba2-5319-43a8-a44a-9a32e9580831

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_weight_ge_of_locallyMinimal_cycle_bound
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_elementaryBoundaryMoves_subset_middleBoundaryCode

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (weight : Word F ι → Nat)
    (lowerBound : Nat)
    (hlocal : ∀ c : Word F ι, c ∈ K.middleCycleCode.carrier → c ≠ 0 →
      IsLocallyMinimal weight (elementaryBoundaryMoves K) c →
        lowerBound ≤ weight c)
    (c : Word F ι) (hcZ : c ∈ K.middleCycleCode.carrier)
    (hcB : c ∉ K.middleBoundaryCode.carrier) :
    lowerBound ≤ weight c := by
  exact weight_ge_of_locallyMinimal_cycle_bound weight
    K.middleCycleCode.carrier.toAddSubgroup
    K.middleBoundaryCode.carrier.toAddSubgroup (elementaryBoundaryMoves K)
    K.middleBoundaryCode_le_middleCycleCode
    (elementaryBoundaryMoves_subset_middleBoundaryCode K) lowerBound hlocal
    c hcZ hcB
end QEC.Coding.LocallyMinimalDistance
