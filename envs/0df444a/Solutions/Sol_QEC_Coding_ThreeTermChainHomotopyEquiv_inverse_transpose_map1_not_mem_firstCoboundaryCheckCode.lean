-- Prove2me | solution 1 for QEC.Coding.ThreeTermChainHomotopyEquiv.inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:33:37.730573+00:00
-- url     : https://prove2.me/submissions/609425ac-2a83-4445-b161-7b6c1b88d129

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
omit [DecidableEq F]
namespace QEC.Coding.ThreeTermChainHomotopyEquiv
theorem _root_.solution
    (e : ThreeTermChainHomotopyEquiv A B)
    {x : Word F ι1}
    (hxCocycle : x ∈ A.middleCocycleCode.carrier)
    (hxNontrivial : x ∉ A.firstCoboundaryCheckCode.carrier) :
    wordLinearMapTranspose e.inverse.map1 x ∉
      B.firstCoboundaryCheckCode.carrier := by
  intro hTargetCoboundary
  let xCocycle : A.middleCocycleCode.carrier := ⟨x, hxCocycle⟩
  have hSourceClassNe : A.middleCoboundaryInCocycles.mkQ xCocycle ≠ 0 := by
    intro hZero
    have hMem : xCocycle ∈ A.middleCoboundaryInCocycles :=
      (Submodule.Quotient.mk_eq_zero A.middleCoboundaryInCocycles).mp hZero
    exact hxNontrivial hMem
  have hTargetClassZero :
      e.inverse.inducedMiddleCohomology
          (A.middleCoboundaryInCocycles.mkQ xCocycle) = 0 := by
    rw [e.inverse.inducedMiddleCohomology_mk]
    apply (Submodule.Quotient.mk_eq_zero B.middleCoboundaryInCocycles).mpr
    exact hTargetCoboundary
  have hSourceClassZero : A.middleCoboundaryInCocycles.mkQ xCocycle = 0 :=
    e.inducedMiddleCohomologyEquiv.symm.injective (by
      change e.inverse.inducedMiddleCohomology (A.middleCoboundaryInCocycles.mkQ xCocycle) =
        e.inverse.inducedMiddleCohomology 0
      simpa only [map_zero] using hTargetClassZero)
  exact hSourceClassNe hSourceClassZero
end QEC.Coding.ThreeTermChainHomotopyEquiv
