-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_constant_square_root_of_even_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:22.5962+00:00
-- url     : https://prove2.me/submissions/98c2e3df-a2dd-48b9-ba37-3a828cf15b4d

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_square_root_of_even_finrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution
    {F K : Type*} [Field F] [Field K] [Finite K] [Algebra F K]
    (a : F) (hEven : 2 ∣ Module.finrank F K) :
    ∃ r : K, r ^ 2 = algebraMap F K a := by
  by_cases hSquare : ∃ r : F, r ^ 2 = a
  · obtain ⟨r, hr⟩ := hSquare
    exact ⟨algebraMap F K r, by rw [← map_pow, hr]⟩
  · apply exists_square_root_of_even_finrank a _ hEven
    intro r hr
    exact hSquare ⟨r, hr⟩
end QEC.Coding.ExpanderCodes
