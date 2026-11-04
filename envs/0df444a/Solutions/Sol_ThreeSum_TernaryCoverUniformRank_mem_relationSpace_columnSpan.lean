-- Prove2me | solution 1 for ThreeSum.TernaryCoverUniformRank.mem_relationSpace_columnSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:33.865495+00:00
-- url     : https://prove2.me/submissions/cfd734c9-a910-479c-9133-9802c7a97c3c

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverUniformRank
open Finset TernaryCoverRelations
open scoped BigOperators
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
namespace ThreeSum.TernaryCoverUniformRank
theorem _root_.solution {d : ℕ} (v : Fin d → σ → K) (a : Fin d → K) :
    a ∈ relationSpace (columnSpan v) ↔ ∀ i, ∑ j, a j * v j i = 0 := by
  change dotProductEquiv K (Fin d) a ∈ (columnSpan v).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span (Set.mem_range_self i))
  · intro h x hx
    have hs : columnSpan v ≤ LinearMap.ker (dotProductEquiv K (Fin d) a) := by
      apply Submodule.span_le.mpr
      rintro w ⟨i, rfl⟩
      exact h i
    exact hs hx
end ThreeSum.TernaryCoverUniformRank
