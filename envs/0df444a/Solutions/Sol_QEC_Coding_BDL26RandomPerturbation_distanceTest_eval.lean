-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.distanceTest_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:32.703168+00:00
-- url     : https://prove2.me/submissions/cb8dd8dc-7870-4b62-9fe0-e80cf9348bba

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dotExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_subExpr_eval
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
theorem _root_.solution (b : VecExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ)
    (x : Space) (hx : ∀ j, (b j).eval a z ρ = x j) (hρ : 0 ≤ ρ) :
    (distanceTest b).eval a z ρ = true ↔ dist z x ≤ ρ := by
  have hd := subExpr_eval centerExpr b a z ρ z x (fun _ => rfl) hx
  have hdd := dotExpr_eval _ _ a z ρ _ _ hd hd
  simp only [distanceTest,RealTest.eval,RealExpr.eval,hdd,decide_eq_true_eq,
    real_inner_self_eq_norm_sq]
  rw [dist_eq_norm]
  constructor
  · intro h; nlinarith [norm_nonneg (z-x)]
  · intro h; nlinarith [norm_nonneg (z-x)]
end QEC.Coding.BDL26RandomPerturbation
