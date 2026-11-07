-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.exists_nonzero_mem_of_extendedMinimumDistance_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:13:57.767927+00:00
-- url     : https://prove2.me/submissions/a4bc314b-e18c-44e2-9f6a-45945984fa7d

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedMinimumDistance_eq_top_iff


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {A : Type u}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A]
    (C : LinearCode F A) (hFinite : extendedMinimumDistance C ≠ ⊤) :
    ∃ x, x ∈ C.carrier ∧ x ≠ 0 := by
  have hNeBot : C.carrier ≠ ⊥ := by
    intro hBot
    exact hFinite ((extendedMinimumDistance_eq_top_iff C).2 hBot)
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hNeBot with ⟨x, hx, hx0⟩
  exact ⟨x, hx, hx0⟩
end QEC.Coding.HypergraphProduct
