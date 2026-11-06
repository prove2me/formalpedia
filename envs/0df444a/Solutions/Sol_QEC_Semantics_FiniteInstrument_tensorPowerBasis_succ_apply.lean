-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:49:02.536571+00:00
-- url     : https://prove2.me/submissions/70ce2eea-8599-4f01-af0a-34336750ace3

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (b : OrthonormalBasis β Complex H)
    (attempts : Nat) (head : β) (tail : tensorPowerHistory β attempts) :
    tensorPowerBasis b (attempts + 1) (head, tail) =
      b head ⊗ₜ[Complex] tensorPowerBasis b attempts tail := by
  change (b.tensorProduct (tensorPowerBasis b attempts)) (head, tail) =
    b head ⊗ₜ[Complex] tensorPowerBasis b attempts tail
  exact OrthonormalBasis.tensorProduct_apply b (tensorPowerBasis b attempts) head tail
end QEC.Semantics.FiniteInstrument
