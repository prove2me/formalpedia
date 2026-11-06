-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.trace_rankOne_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:57:04.334211+00:00
-- url     : https://prove2.me/submissions/896043d0-1394-4dcc-beed-cb3320ba5dd6

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_rankOne

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (E : Operator H) (x y : H) :
    LinearMap.trace Complex H
      ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) =
      inner Complex y (E x) := by
  calc
    LinearMap.trace Complex H
        ((InnerProductSpace.rankOne Complex x y).toLinearMap.comp E) =
        LinearMap.trace Complex H
          (E.comp (InnerProductSpace.rankOne Complex x y).toLinearMap) :=
            (LinearMap.trace_comp_comm'
              (InnerProductSpace.rankOne Complex x y).toLinearMap E).symm
    _ = inner Complex y (E x) := trace_comp_rankOne E x y
end QEC.Semantics.QuditSubsystem
