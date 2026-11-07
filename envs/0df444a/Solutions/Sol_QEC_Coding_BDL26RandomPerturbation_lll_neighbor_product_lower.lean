-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.lll_neighbor_product_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:00.7339+00:00
-- url     : https://prove2.me/submissions/92be3b25-1af2-4eb8-81c7-17d7ab324f0f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_mul
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {I : Type*} (D : ℕ) (s : Finset I)
    (hcard : s.card ≤ D) :
    (1/2 : ℝ) ≤ ∏ _i ∈ s, (1-lllWeight D) := by
  have hx := lllWeight_bounds D
  have hd : (s.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_right hd hx.1.le
  have he := lllWeight_mul D
  have hsmall : (s.card : ℝ)*lllWeight D ≤ 1/2 := by nlinarith
  have hb := one_add_mul_le_pow (a := -lllWeight D) (by linarith : -2 ≤ -lllWeight D) s.card
  rw [Finset.prod_const]
  have hb' : 1-(s.card : ℝ)*lllWeight D ≤ (1-lllWeight D)^s.card := by
    simpa only [sub_eq_add_neg,mul_neg] using hb
  linarith
end QEC.Coding.BDL26RandomPerturbation
