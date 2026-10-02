-- Prove2me | solution 1 for TheoryOfGames.Decomposition.splitting_empty_univ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:17:11.845153+00:00
-- url     : https://prove2.me/submissions/e3f2956c-beb1-45ed-8ca7-85944a7543a9

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    IsSplitting v ∅ ∧ IsSplitting v Finset.univ := by
  refine ⟨?_, ?_⟩
  · intro S T hS _
    have : S = ∅ := Finset.subset_empty.mp hS
    subst this
    simp [hv.empty]
  · intro S T _ hT
    have : T = ∅ := by simpa using hT
    subst this
    simp [hv.empty]
