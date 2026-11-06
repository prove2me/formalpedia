-- Prove2me | solution 1 for QEC.Locality.unitaryTransport_toQuantumChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:24.781169+00:00
-- url     : https://prove2.me/submissions/f735cdd1-6d39-4448-ab93-ccafdbf9c9ac

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_quantumChannel_ext
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport


set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {κ : Type v} [Fintype κ]
    {H K Ht Kt : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] [NormedAddCommGroup Ht] [InnerProductSpace Complex Ht]
    [FiniteQuantumSystem Ht] [NormedAddCommGroup Kt] [InnerProductSpace Complex Kt]
    [FiniteQuantumSystem Kt] (E : FiniteKrausFamily κ H K)
    (U : UnitaryTransport H Ht) (V : UnitaryTransport K Kt) (hE : E.Complete) :
    (E.unitaryTransport U V).toQuantumChannel
        (E.unitaryTransport_complete U V hE) =
      QuantumChannel.comp (QuantumChannel.unitaryConj V)
        (QuantumChannel.comp (E.toQuantumChannel hE)
          (QuantumChannel.unitaryConj U.symm)) := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  rw [FiniteKrausFamily.toQuantumChannel_apply_sum]
  change (E.unitaryTransport U V).inducedMap A = _
  rw [FiniteKrausFamily.unitaryTransport_inducedMap_apply]
  change V.conjOperator (E.inducedMap (U.symm.conjOperator A)) =
    V.conjOperator ((E.toQuantumChannel hE) (U.symm.conjOperator A))
  congr 1
end QEC.Locality
