-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.traceNorm_comp_apply_le_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:26.325209+00:00
-- url     : https://prove2.me/submissions/78c86ffd-e55d-4b19-ab94-d6f507fad2b4

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Theorems.Thm_QEC_Semantics_QuantumChannel_map_isSymmetric
import Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_apply_le_of_isSymmetric

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
theorem _root_.solution
    [Nontrivial H] [Nontrivial K] [Nontrivial L]
    (Psi : QuantumChannel K L) (Phi : QuantumChannel H K)
    (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm ((comp Psi Phi) A) ≤ traceNorm A := by
  change traceNorm (Psi (Phi A)) ≤ traceNorm A
  calc
    traceNorm (Psi (Phi A)) ≤ traceNorm (Phi A) :=
      Psi.traceNorm_apply_le_of_isSymmetric (Phi A) (Phi.map_isSymmetric hA)
    _ ≤ traceNorm A := Phi.traceNorm_apply_le_of_isSymmetric A hA
end QEC.Semantics.QuantumChannel
