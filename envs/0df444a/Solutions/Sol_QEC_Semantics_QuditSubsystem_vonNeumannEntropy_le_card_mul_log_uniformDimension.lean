-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.vonNeumannEntropy_le_card_mul_log_uniformDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:14:58.067037+00:00
-- url     : https://prove2.me/submissions/0da29e72-0432-4a81-b04e-6c11fa4b4abd

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_QuditSubsystem_vonNeumannEntropy_le_sum_log_selectedDimensions
import Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_log_selectedDimensions_le_card_mul_log_uniformDimension

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (hq : forall i, 0 < q i) (D : Nat)
    (hD : forall i, i ∈ S.selected -> q i <= D) (rho : DensityOperator S.selectedSystem) :
    rho.vonNeumannEntropy <= (S.selected.card : Real) * Real.logb 2 (D : Real) := by
  exact (S.vonNeumannEntropy_le_sum_log_selectedDimensions rho).trans
    (S.sum_log_selectedDimensions_le_card_mul_log_uniformDimension hq D hD)
end QEC.Semantics.QuditSubsystem
