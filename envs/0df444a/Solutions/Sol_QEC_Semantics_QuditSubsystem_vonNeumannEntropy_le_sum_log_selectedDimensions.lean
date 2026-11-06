-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.vonNeumannEntropy_le_sum_log_selectedDimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:33:10.739579+00:00
-- url     : https://prove2.me/submissions/bc8a1817-7374-47f3-8082-aa073b3d9e4d

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_le_log_finrank
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedDimensions_positive_of_density
import Theorems.Thm_QEC_Semantics_QuditSubsystem_log_finrank_selectedSystem_eq_sum_log_selectedDimensions

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
    rho.vonNeumannEntropy <= ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by
  calc
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex S.selectedSystem : Real) :=
      rho.vonNeumannEntropy_le_log_finrank
    _ = ∑ i ∈ S.selected, Real.logb 2 (q i : Real) :=
      S.log_finrank_selectedSystem_eq_sum_log_selectedDimensions
        (S.selectedDimensions_positive_of_density rho)
end QEC.Semantics.QuditSubsystem
