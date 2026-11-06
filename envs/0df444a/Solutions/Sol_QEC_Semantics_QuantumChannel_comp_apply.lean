-- Prove2me | solution 1 for QEC.Semantics.QuantumChannel.comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:46:38.333674+00:00
-- url     : https://prove2.me/submissions/0e2e4b35-c164-4850-9e31-aa3c644f8622

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
theorem _root_.solution {L : Type u} [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K)
    (A : Operator H) : (comp Ψ Φ) A = Ψ (Φ A) :=
  rfl
end QEC.Semantics.QuantumChannel
