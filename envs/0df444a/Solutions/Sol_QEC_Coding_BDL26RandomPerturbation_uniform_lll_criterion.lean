-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.uniform_lll_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:14.102036+00:00
-- url     : https://prove2.me/submissions/7ac4797a-c823-4367-8865-6fae7c5cf820

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Parameters
import Mathlib.Algebra.Order.Ring.Pow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lll_neighbor_product_lower

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {I : Type*} (D : ℕ) (s : Finset I)
    (hcard : s.card ≤ D) {p : ℝ} (hp : p ≤ 1/(4*((D : ℝ)+1))) :
    p ≤ lllWeight D * ∏ _i ∈ s, (1-lllWeight D) := by
  have hx := lllWeight_bounds D
  have hprod := mul_le_mul_of_nonneg_left (lll_neighbor_product_lower D s hcard) hx.1.le
  have he : (1 : ℝ)/(4*((D : ℝ)+1)) = lllWeight D*(1/2) := by
    have hd : (D : ℝ)+1 ≠ 0 := by positivity
    unfold lllWeight
    field_simp [hd]
    <;> ring
  calc
    p ≤ 1/(4*((D : ℝ)+1)) := hp
    _ = lllWeight D*(1/2) := he
    _ ≤ _ := hprod
end QEC.Coding.BDL26RandomPerturbation
