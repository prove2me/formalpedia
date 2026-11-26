-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_le_two_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:25:00.686438+00:00
-- url     : https://prove2.me/submissions/79e013d1-de37-4b0a-a299-6d118605f135

module
public import Definitions.Def_SemigroupBetti_Exceptional
public import Definitions.Def_SemigroupBetti_Main
public import Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_W_exceptional
public import Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_W_of_ne
public import Theorems.Thm_SemigroupBetti_GenData_st_eq_one_one_iff


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.beta1 ≤ 2 * G.W := by
  by_cases h : (G.s, G.t) = (1, 1)
  · obtain ⟨hA, hB⟩ := G.st_eq_one_one_iff.1 h
    exact G.beta1_le_two_W_exceptional hA hB
  · exact G.beta1_le_two_W_of_ne h
end SemigroupBetti.GenData
