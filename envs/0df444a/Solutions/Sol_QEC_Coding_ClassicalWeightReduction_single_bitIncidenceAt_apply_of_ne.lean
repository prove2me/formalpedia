-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.single_bitIncidenceAt_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:38.806454+00:00
-- url     : https://prove2.me/submissions/36085f44-00ad-4f75-80a7-865b27042bbf

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution {b : Bit} (e : Incidence R)
    (hb : e.1.2 ≠ b) (k : Fin (Fintype.card (BitNeighbor R b))) :
    (Pi.single (Sum.inl (bitIncidenceAt R b k)) 1 :
        Word F (WeightReducedBit R)) (Sum.inl e) = 0 := by
  classical
  have he : bitIncidenceAt R b k ≠ e := by
    intro h
    apply hb
    have hv := congrArg (fun x : Incidence R => x.1.2) h
    simpa [bitIncidenceAt] using hv.symm
  simp [he]
end QEC.Coding.ClassicalWeightReduction
