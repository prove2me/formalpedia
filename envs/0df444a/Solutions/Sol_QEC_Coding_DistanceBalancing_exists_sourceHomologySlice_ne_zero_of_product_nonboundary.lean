-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.exists_sourceHomologySlice_ne_zero_of_product_nonboundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:53:58.263384+00:00
-- url     : https://prove2.me/submissions/b19e8d94-c845-43ae-90c5-770bb038dac1

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_sourceHomologySlice_ne_zero_iff
import Theorems.Thm_QEC_Coding_DistanceBalancing_mem_middleBoundaryCode_of_slices

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hNonboundary : z ∉ (chainComplex D).middleBoundaryCode.carrier) :
    ∃ a : classicalBit, sourceHomologySlice D z hz a ≠ 0 := by
  by_contra hNone
  have hAll : ∀ a : classicalBit,
      xOneBitSlice z a ∈
        (sourceChainComplex D).middleBoundaryCode.carrier := by
    intro a
    by_contra ha
    apply hNone
    exact ⟨a, (sourceHomologySlice_ne_zero_iff D z hz a).2 ha⟩
  exact hNonboundary
    (mem_middleBoundaryCode_of_slices D S hS z hz hAll)
end QEC.Coding.DistanceBalancing
