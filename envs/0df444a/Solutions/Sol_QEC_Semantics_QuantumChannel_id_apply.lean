-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.id_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:47:17.071201+00:00
-- url     : https://prove2.me/submissions/1b3c4aad-4744-4915-b2e3-208914cc2264

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.QuantumChannel
theorem _root_.solution (A : Operator H) : (id H) A = A :=
  rfl
end QEC.Semantics.QuantumChannel
