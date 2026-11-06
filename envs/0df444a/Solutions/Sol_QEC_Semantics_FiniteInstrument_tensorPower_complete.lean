-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:20:27.756942+00:00
-- url     : https://prove2.me/submissions/2e3cac89-4cd4-41f2-ade8-a3eceab090b1

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorUnitInstrument_complete

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
    (hI : I.kraus.Complete) (n : Nat) :
    (I.tensorPower n).kraus.Complete := by
  induction n with
  | zero => exact tensorUnitInstrument_complete
  | succ n ih => exact I.tensor_complete (I.tensorPower n) hI ih
end QEC.Semantics.FiniteInstrument
