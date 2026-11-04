-- Prove2me | solution 1 for ThreeSum.TernaryCoverRelations.paired_possibleSpans_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:08.440956+00:00
-- url     : https://prove2.me/submissions/8416fd8a-5804-4f5a-ba0d-35ea036ffc45

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Theorems.Thm_ThreeSum_TernaryCoverRelations_possibleSpans_card

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRelations
open Finset
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryCoverRelations
theorem _root_.solution (k : ℕ) :
    (possibleSpans K (2 * k)).card ≤ 3 ^ (4 * k ^ 2) := by
  convert possibleSpans_card (K := K) (2 * k) using 1 <;> ring
end ThreeSum.TernaryCoverRelations
