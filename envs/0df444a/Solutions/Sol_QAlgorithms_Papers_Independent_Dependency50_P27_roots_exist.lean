-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.roots_exist
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:20:40.038998+00:00
-- url     : https://prove2.me/submissions/6e4ad400-6094-4278-ae2f-089d05fb0291

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) :
    ∃ s : List R, s.Pairwise (· < ·) ∧
      ((p = 0 ∧ s = []) ∨ (p ≠ 0 ∧ rootsOn p a b s)) := by
  by_cases hp : p = 0
  · exact ⟨[], List.Pairwise.nil, Or.inl ⟨hp, rfl⟩⟩
  refine ⟨(p.roots.toFinset.filter (fun x => a < x ∧ x < b)).sort, (Finset.sortedLT_sort _).pairwise,
    Or.inr ⟨hp, fun x => ?_⟩⟩
  rw [Finset.mem_sort, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  tauto

end
