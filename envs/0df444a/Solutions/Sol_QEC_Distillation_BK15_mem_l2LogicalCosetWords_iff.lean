-- Prove2me | solution 1 for QEC.Distillation.BK15.mem_l2LogicalCosetWords_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:34.809192+00:00
-- url     : https://prove2.me/submissions/bee735b4-ed6b-4489-ad7f-363dbce652d9

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
    w ∈ l2LogicalCosetWords ↔
      ∃ b : Sum (Fin 4) QuadraticIndex → Bit, w = l2CoefficientMap b + allOnes := by
  constructor
  · intro hw
    rw [l2LogicalCosetWords, Finset.mem_image] at hw
    rcases hw with ⟨u, hu, huEq⟩
    rw [l2Words, Finset.mem_image] at hu
    rcases hu with ⟨b, -, hbEq⟩
    exact ⟨b, by simpa [hbEq] using huEq.symm⟩
  · rintro ⟨b, rfl⟩
    rw [l2LogicalCosetWords, Finset.mem_image]
    refine ⟨l2CoefficientMap b, ?_, rfl⟩
    rw [l2Words, Finset.mem_image]
    exact ⟨b, Finset.mem_univ _, rfl⟩
end QEC.Distillation.BK15
