-- Prove2me | solution 1 for QEC.Coding.FiberBundle.weightReductionForwardMap1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:49:58.955197+00:00
-- url     : https://prove2.me/submissions/03089cbb-c305-4aea-a5ae-8b8946f41786

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_basis_weight_le
import Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (x : Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne)) :
    HammingWeight (weightReductionForwardMap1 D h x) ≤
      L * HammingWeight x := by
  classical
  apply HammingWeight_linearMap_le_of_basis
  intro q
  change HammingWeight
      (weightReductionForwardMap1 D h (reducedQubitBasisWord D q)) ≤ L
  exact weightReductionForwardMap1_basis_weight_le
    D h hOne hBitDegree q
end QEC.Coding.FiberBundle
