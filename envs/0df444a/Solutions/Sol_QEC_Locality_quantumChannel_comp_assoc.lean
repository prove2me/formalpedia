-- Prove2me | solution 1 for QEC.Locality.quantumChannel_comp_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:26.567945+00:00
-- url     : https://prove2.me/submissions/7c4b57f6-31ef-4db1-a21e-07fa4f885f84

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_quantumChannel_ext

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {H K L M : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    [NormedAddCommGroup M] [InnerProductSpace Complex M] [FiniteQuantumSystem M]
    (Phi : QuantumChannel H K) (Psi : QuantumChannel K L) (Omega : QuantumChannel L M) :
    QuantumChannel.comp Omega (QuantumChannel.comp Psi Phi) =
      QuantumChannel.comp (QuantumChannel.comp Omega Psi) Phi := by
  apply quantumChannel_ext
  rfl
end QEC.Locality
