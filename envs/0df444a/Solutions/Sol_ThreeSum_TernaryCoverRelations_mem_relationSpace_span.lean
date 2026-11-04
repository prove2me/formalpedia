-- Prove2me | solution 1 for ThreeSum.TernaryCoverRelations.mem_relationSpace_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:31.199244+00:00
-- url     : https://prove2.me/submissions/aff037a0-07ba-4107-afe3-2554fa617b6e

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryCoverRelations
theorem _root_.solution {d : ℕ} {σ : Type*}
    (columns : σ → Fin d → Fin 3) (a : Fin d → K) :
    a ∈ relationSpace (Submodule.span K (Set.range fun j => digitVector (K := K) (columns j))) ↔
      ∀ j : σ, ∑ i, a i * digitVector (K := K) (columns j) i = 0 := by
  classical
  change dotProductEquiv K (Fin d) a ∈
    (Submodule.span K (Set.range fun j => digitVector (K := K) (columns j))).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h j
    exact h _ (Submodule.subset_span (Set.mem_range_self j))
  · intro h v hv
    have hs : Submodule.span K (Set.range fun j => digitVector (K := K) (columns j)) ≤
        LinearMap.ker (dotProductEquiv K (Fin d) a) := by
      apply Submodule.span_le.mpr
      rintro w ⟨j, rfl⟩
      exact h j
    exact hs hv
end ThreeSum.TernaryCoverRelations
