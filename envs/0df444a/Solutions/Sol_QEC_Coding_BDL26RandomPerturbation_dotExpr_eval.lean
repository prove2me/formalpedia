-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.dotExpr_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:12:38.633474+00:00
-- url     : https://prove2.me/submissions/d8cf54ad-15fd-43c0-b368-f32a4117712d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (b c : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x y : Space) (hx : ∀ j, (b j).eval a z ρ = x j)
    (hy : ∀ j, (c j).eval a z ρ = y j) :
    (dotExpr b c).eval a z ρ = inner ℝ x y := by
  simp only [dotExpr,RealExpr.eval,hx,hy,PiLp.inner_apply,Real.inner_apply,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl
end QEC.Coding.BDL26RandomPerturbation
