-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorProduct_matrixEntry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:35:47.095098+00:00
-- url     : https://prove2.me/submissions/fdf490a5-b552-4892-8515-59e0587559b6

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
omit [Fintype Ω]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts)
      (left right : tensorPowerHistory β attempts),
      inner Complex (tensorPowerBasis basis attempts left)
          (tensorPowerBranchOperatorProduct branch unit attempts history
            (tensorPowerBasis basis attempts right)) =
        tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history left right := by
  intro attempts
  induction attempts with
  | zero =>
      intro history left right
      rfl
  | succ attempts ih =>
      rintro ⟨outcome, tailHistory⟩ ⟨leftHead, leftTail⟩
        ⟨rightHead, rightTail⟩
      change inner Complex
        ((basis.tensorProduct (tensorPowerBasis basis attempts)) (leftHead, leftTail))
        ((TensorProduct.map (branch outcome)
          (tensorPowerBranchOperatorProduct branch unit attempts tailHistory))
          ((basis.tensorProduct (tensorPowerBasis basis attempts)) (rightHead, rightTail))) =
        inner Complex (basis leftHead) (branch outcome (basis rightHead)) *
          tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
            tailHistory leftTail rightTail
      rw [OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.tensorProduct_apply]
      rw [TensorProduct.map_tmul, TensorProduct.inner_tmul]
      rw [ih tailHistory leftTail rightTail]
end QEC.Semantics.FiniteInstrument
