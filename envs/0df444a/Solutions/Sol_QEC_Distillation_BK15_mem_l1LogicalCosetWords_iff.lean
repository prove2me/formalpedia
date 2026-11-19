-- Prove2me | solution 1 for QEC.Distillation.BK15.mem_l1LogicalCosetWords_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:38.073742+00:00
-- url     : https://prove2.me/submissions/4e96a69b-8ba3-4123-8dd3-bcafcb85baa9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (w : Word) :
    w ∈ l1LogicalCosetWords ↔
      ∃ a : Fin 4 → Bit, w = l1CoefficientMap a + allOnes := by
  constructor
  · intro hw
    rw [l1LogicalCosetWords, Finset.mem_image] at hw
    rcases hw with ⟨u, hu, huEq⟩
    rw [l1Words, Finset.mem_image] at hu
    rcases hu with ⟨a, -, haEq⟩
    exact ⟨a, by simpa [haEq] using huEq.symm⟩
  · rintro ⟨a, rfl⟩
    rw [l1LogicalCosetWords, Finset.mem_image]
    refine ⟨l1CoefficientMap a, ?_, rfl⟩
    rw [l1Words, Finset.mem_image]
    exact ⟨a, Finset.mem_univ _, rfl⟩
end QEC.Distillation.BK15
