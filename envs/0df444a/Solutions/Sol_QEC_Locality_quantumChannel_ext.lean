-- Prove2me | solution 1 for QEC.Locality.quantumChannel_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:38:02.965492+00:00
-- url     : https://prove2.me/submissions/502603ae-5b07-4685-ae3c-c3951c8e9021

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {H K : Type u} [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {Phi Psi : QuantumChannel H K} (h : Phi.toLinearMap = Psi.toLinearMap) :
    Phi = Psi := by
  cases Phi
  cases Psi
  cases h
  rfl
end QEC.Locality
