-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_regularizedMax_c2_example_real_line_412956b291f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:48.706194+00:00
-- url     : https://prove2.me/submissions/01f53f8a-7343-4733-b221-58b5030d65d8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_RegularizedMaxConvergenceC2_proof_f4030eb08b08
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution :
    TendstoC2On (fun t x => regMax t (fun j : Fin 2 => x ^ 2 + ((j : ℕ) : ℝ) * t) + t / 2)
      (fun x : ℝ => x ^ 2) (Set.Icc (-1) 1) := by
  have hd1 : ∀ c : ℝ, fderiv ℝ (fun x : ℝ => x ^ 2 + c) = fderiv ℝ (fun x : ℝ => x ^ 2) :=
    fun c => funext fun y => fderiv_add_const c
  refine RegularizedMaxConvergenceC2.proof (Fin 2) Set.univ (Set.Icc (-1) 1) (fun x : ℝ => x ^ 2)
    (fun t j x => x ^ 2 + ((j : ℕ) : ℝ) * t) (fun t => t) (fun _ => 0) isOpen_univ
    (Set.subset_univ _) (by fun_prop) ?_ ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact ⟨ht, fun j => by fun_prop⟩
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · intro j
    refine ⟨Metric.tendstoUniformlyOn_iff.2 fun e he => ?_, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds he)]
        with t (ht : 0 < t) hte
      intro x _
      have hj : ((j : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [Real.dist_eq, abs_sub_comm, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      nlinarith
    · simp only [hd1]
      exact tendstoUniformlyOn_self _ _ _
    · simp only [hd1]
      exact tendstoUniformlyOn_self _ _ _
  · exact Eventually.of_forall fun t j x _ => by simp
  · simp
end GroundTheory.Heights₂.Heights.AnalyticLimit
