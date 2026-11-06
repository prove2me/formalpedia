-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.selectedDimensions_positive_of_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:57.988786+00:00
-- url     : https://prove2.me/submissions/6642cd0e-761f-4af3-9948-83dc79f1b082

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_finrank_pos
import Theorems.Thm_QEC_Semantics_QuditSubsystem_finrank_selectedSystem_eq_prod_selectedDimensions

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
    (rho : DensityOperator S.selectedSystem) :
    forall i, i ∈ S.selected -> 0 < q i := by
  have hfinrank := DensityOperator.finrank_pos rho
  have hproduct : 0 < ∏ i ∈ S.selected, q i := by
    rw [← S.finrank_selectedSystem_eq_prod_selectedDimensions]
    exact hfinrank
  intro i hi
  exact Nat.pos_of_ne_zero ((Finset.prod_ne_zero_iff.mp (Nat.ne_of_gt hproduct)) i hi)
end QEC.Semantics.QuditSubsystem
