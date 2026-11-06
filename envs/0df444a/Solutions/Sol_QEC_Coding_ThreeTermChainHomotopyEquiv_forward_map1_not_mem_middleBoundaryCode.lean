-- Prove2me | solution 1 for QEC.Coding.ThreeTermChainHomotopyEquiv.forward_map1_not_mem_middleBoundaryCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:32:17.718217+00:00
-- url     : https://prove2.me/submissions/bc5ae41e-e8e0-44d3-9a48-3b56e45a0421

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding
universe u v w
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
omit [DecidableEq F] [Fintype ι0] [Fintype ι2] [Fintype κ0] [Fintype κ2]
namespace QEC.Coding.ThreeTermChainHomotopyEquiv
theorem _root_.solution
    (e : ThreeTermChainHomotopyEquiv A B)
    {z : Word F ι1}
    (hzCycle : z ∈ A.middleCycleCode.carrier)
    (hzNontrivial : z ∉ A.middleBoundaryCode.carrier) :
    e.forward.map1 z ∉ B.middleBoundaryCode.carrier := by
  intro hTargetBoundary
  let zCycle : A.middleCycleCode.carrier := ⟨z, hzCycle⟩
  have hSourceClassNe : A.middleBoundaryInCycles.mkQ zCycle ≠ 0 := by
    intro hZero
    have hMem : zCycle ∈ A.middleBoundaryInCycles :=
      (Submodule.Quotient.mk_eq_zero A.middleBoundaryInCycles).mp hZero
    exact hzNontrivial hMem
  have hTargetClassZero :
      e.forward.inducedMiddleHomology
          (A.middleBoundaryInCycles.mkQ zCycle) = 0 := by
    rw [e.forward.inducedMiddleHomology_mk]
    apply (Submodule.Quotient.mk_eq_zero B.middleBoundaryInCycles).mpr
    exact hTargetBoundary
  have hSourceClassZero : A.middleBoundaryInCycles.mkQ zCycle = 0 :=
    e.inducedMiddleHomologyEquiv.injective (by
      change e.forward.inducedMiddleHomology (A.middleBoundaryInCycles.mkQ zCycle) =
        e.forward.inducedMiddleHomology 0
      simpa only [map_zero] using hTargetClassZero)
  exact hSourceClassNe hSourceClassZero
end QEC.Coding.ThreeTermChainHomotopyEquiv
