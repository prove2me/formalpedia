-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_kraus_operator_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:49:41.738226+00:00
-- url     : https://prove2.me/submissions/8c5bed4b-61f6-4c37-8fb4-33e52bffe70a

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (n : Nat) (head : κ) (tail : tensorPowerHistory κ n) :
    (I.tensorPower (n + 1)).kraus.operator (head, tail) =
      TensorProduct.map (I.kraus.operator head)
        ((I.tensorPower n).kraus.operator tail) :=
  rfl
end QEC.Semantics.FiniteInstrument
