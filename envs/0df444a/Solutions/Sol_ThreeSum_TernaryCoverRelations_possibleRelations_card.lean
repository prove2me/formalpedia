-- Prove2me | solution 1 for ThreeSum.TernaryCoverRelations.possibleRelations_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:09.966367+00:00
-- url     : https://prove2.me/submissions/3092014e-1142-46b9-85ea-6b7668678242

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
theorem _root_.solution (d : ℕ) :
    (possibleRelations K d).card ≤ 3 ^ (d * d) := by
  classical
  exact (Finset.card_image_le).trans (possibleSpans_card d)
end ThreeSum.TernaryCoverRelations
