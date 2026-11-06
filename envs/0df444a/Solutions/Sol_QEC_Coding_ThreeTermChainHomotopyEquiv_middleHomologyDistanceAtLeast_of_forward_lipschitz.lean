-- Prove2me | solution 1 for QEC.Coding.ThreeTermChainHomotopyEquiv.middleHomologyDistanceAtLeast_of_forward_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:02.461208+00:00
-- url     : https://prove2.me/submissions/2c5d0f10-3b20-43c6-a4cf-20c89c97751a

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_forward_map1_not_mem_middleBoundaryCode

set_option autoImplicit false
open QEC QEC.Coding
universe u v w
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
namespace QEC.Coding.ThreeTermChainHomotopyEquiv
theorem _root_.solution
    (e : ThreeTermChainHomotopyEquiv A B)
    {d L : Nat}
    (hTarget : MiddleHomologyDistanceAtLeast B d)
    (hLipschitz : ∀ z : Word F ι1,
      HammingWeight (e.forward.map1 z) ≤ L * HammingWeight z) :
    MiddleHomologyDistanceAtLeast A (d / L) := by
  change ∀ z : Word F ι1,
    z ∈ A.middleCycleCode.carrier →
    z ∉ A.middleBoundaryCode.carrier →
    d / L ≤ HammingWeight z
  intro z hzCycle hzNontrivial
  apply Nat.div_le_of_le_mul
  exact (hTarget (e.forward.map1 z)
    (e.forward.mapMiddleCycle ⟨z, hzCycle⟩).2
    (e.forward_map1_not_mem_middleBoundaryCode hzCycle hzNontrivial)).trans
      (hLipschitz z)
end QEC.Coding.ThreeTermChainHomotopyEquiv
