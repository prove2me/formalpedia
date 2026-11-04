-- Prove2me | solution 1 for ThreeSum.TernaryCoverRelations.actual_relation_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:32.794591+00:00
-- url     : https://prove2.me/submissions/53831c75-fbb3-46fe-a225-d26b17173db1

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Theorems.Thm_ThreeSum_TernaryCoverRelations_span_mem_possibleSpans

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryCoverRelations
theorem _root_.solution {d : ℕ} {σ : Type*} (columns : σ → Fin d → Fin 3) :
    relationSpace (Submodule.span K (Set.range fun j => digitVector (K := K) (columns j))) ∈
      possibleRelations K d := by
  classical
  exact mem_image.mpr ⟨_, span_mem_possibleSpans columns, rfl⟩
end ThreeSum.TernaryCoverRelations
