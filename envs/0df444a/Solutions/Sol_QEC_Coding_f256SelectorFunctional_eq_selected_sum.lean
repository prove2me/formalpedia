-- Prove2me | solution 1 for QEC.Coding.f256SelectorFunctional_eq_selected_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:50:19.280696+00:00
-- url     : https://prove2.me/submissions/f12741d2-2ab4-4416-a035-dbc148bf1e34

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Theorems.Thm_QEC_Coding_f256SelectorFunctional_eq_coefficient_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = ∑ q ∈ f256SelectedCoordinates, v q := by
  rw [f256SelectorFunctional_eq_coefficient_sum]
  simp only [f256SelectedCoordinates, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : f256SelectorCoefficient q = 1
  · rw [if_pos h, h, mul_one]
  · have hz : f256SelectorCoefficient q = 0 := by
      apply Fin.ext
      have hlt : (f256SelectorCoefficient q).val < 2 := (f256SelectorCoefficient q).isLt
      have hn : (f256SelectorCoefficient q).val ≠ 1 := by
        intro heq
        exact h (Fin.ext heq)
      change (f256SelectorCoefficient q).val = 0
      omega
    rw [if_neg h, hz, mul_zero]
end QEC.Coding
