-- Prove2me | solution 1 for QEC.Semantics.KnillLaflamme.unitaryTransport_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:43:27.300229+00:00
-- url     : https://prove2.me/submissions/529e755c-c3c4-4cd9-81d9-57ce5fa675d0

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport
import Theorems.Thm_QEC_Semantics_KnillLaflamme_of_unitaryTransport

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
open QEC.Semantics.KnillLaflamme
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
namespace QEC.Semantics.KnillLaflamme
theorem _root_.solution
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D) :
    KnillLaflammeCriterion H C errors ↔
      KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors) := by
  constructor
  · exact unitaryTransport U hCD
  · exact of_unitaryTransport U hCD
end QEC.Semantics.KnillLaflamme
