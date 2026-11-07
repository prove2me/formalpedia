-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleQuery_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:10.342018+00:00
-- url     : https://prove2.me/submissions/83bebccc-6e01-4c14-9c17-5c519c10c46e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleQueryProgram_correct
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (triangleQuery a z ρ).1 = true ↔
      ∃ y ∈ convexHull ℝ (Set.range a), dist y z ≤ ρ := by
  rw [triangleQuery,RealTest.run_value,triangleQueryProgram_correct a z hρ]
end QEC.Coding.BDL26RandomPerturbation
