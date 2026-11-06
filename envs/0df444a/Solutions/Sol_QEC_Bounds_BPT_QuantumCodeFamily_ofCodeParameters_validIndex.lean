-- Prove2me | solution 1 for QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_validIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:57.899902+00:00
-- url     : https://prove2.me/submissions/fc450f48-a127-4ef6-9758-453943e8ce1c

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound

set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeFamily
namespace QEC.Bounds.BPT.QuantumCodeFamily
theorem _root_.solution {F : Type u} {ι : Nat → Type v} [Field F]
    [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    (ofCodeParameters codeParameters validIndex).validIndex n = validIndex n :=
  rfl
end QEC.Bounds.BPT.QuantumCodeFamily
