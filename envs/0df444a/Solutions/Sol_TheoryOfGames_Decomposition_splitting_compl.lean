-- Prove2me | solution 1 for TheoryOfGames.Decomposition.splitting_compl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:08:52.743442+00:00
-- url     : https://prove2.me/submissions/f12df0c7-9637-4620-a845-f214db1de556

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J : Finset ι) :
    IsSplitting v J ↔ IsSplitting v Jᶜ := by
  constructor
  · intro h S T hS hT
    rw [compl_compl] at hT
    rw [Finset.union_comm, h T S hT hS, add_comm]
  · intro h S T hS hT
    have hS' : S ⊆ Jᶜᶜ := by rwa [compl_compl]
    rw [Finset.union_comm, h T S hT hS', add_comm]
