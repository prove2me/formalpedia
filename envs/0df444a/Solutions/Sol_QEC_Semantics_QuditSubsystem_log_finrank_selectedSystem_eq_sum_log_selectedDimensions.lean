-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.log_finrank_selectedSystem_eq_sum_log_selectedDimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:14:58.605198+00:00
-- url     : https://prove2.me/submissions/661ee64b-71b9-439c-abe4-e6a4d3ca0c96

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
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
    (hq : forall i, i ∈ S.selected -> 0 < q i) :
    Real.logb 2 (Module.finrank Complex S.selectedSystem : Real) =
      ∑ i ∈ S.selected, Real.logb 2 (q i : Real) := by
  rw [S.finrank_selectedSystem_eq_prod_selectedDimensions]
  push_cast
  exact Real.logb_prod S.selected (fun i => (q i : Real)) (fun i hi => by
    change (q i : Real) ≠ 0
    exact_mod_cast Nat.ne_of_gt (hq i hi))
end QEC.Semantics.QuditSubsystem
