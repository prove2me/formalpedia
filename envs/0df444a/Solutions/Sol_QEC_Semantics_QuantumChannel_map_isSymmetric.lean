-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.map_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:53:15.757407+00:00
-- url     : https://prove2.me/submissions/2c347bb7-84e7-4f0b-acb1-23590e0dbf0b

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Theorems.Thm_QEC_Semantics_negativePart_positive
import Theorems.Thm_QEC_Semantics_positivePart_positive
import Theorems.Thm_QEC_Semantics_positivePart_sub_negativePart


set_option autoImplicit false
universe u
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.QuantumChannel
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (Phi : QuantumChannel H K) {A : Operator H}
    (hA : A.IsSymmetric) : (Phi A).IsSymmetric := by
  have hdecomp := positivePart_sub_negativePart A hA
  rw [← hdecomp, map_sub]
  exact (Phi.map_positive (positivePart_positive A)).isSymmetric.sub
    (Phi.map_positive (negativePart_positive A)).isSymmetric
end QEC.Semantics.QuantumChannel
