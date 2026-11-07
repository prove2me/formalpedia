-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.RealTest.run_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:36.730905+00:00
-- url     : https://prove2.me/submissions/a0e16f65-b290-4a02-aee0-7e3306e4bf7f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_cost_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply


attribute [local simp] QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
attribute [local simp] QEC.Coding.BDL26RandomPerturbation.centerExpr_eval

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
namespace RealTest
theorem _root_.solution (e : RealTest) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).2 ≤ 2*e.cost := by
  induction e with
  | le x y =>
    have hx := x.run_cost_le a z ρ
    have hy := y.run_cost_le a z ρ
    simp only [RealTest.run,RealTest.cost]; omega
  | ne x y =>
    have hx := x.run_cost_le a z ρ
    have hy := y.run_cost_le a z ρ
    simp only [RealTest.run,RealTest.cost]; omega
  | both x y ihx ihy => simp only [RealTest.run,RealTest.cost]; omega
  | either x y ihx ihy => simp only [RealTest.run,RealTest.cost]; omega
end RealTest
end QEC.Coding.BDL26RandomPerturbation
