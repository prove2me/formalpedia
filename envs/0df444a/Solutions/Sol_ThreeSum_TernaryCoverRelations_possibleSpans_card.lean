-- Prove2me | solution 1 for ThreeSum.TernaryCoverRelations.possibleSpans_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:29.148531+00:00
-- url     : https://prove2.me/submissions/2585fcd3-a8ca-437f-9991-0532a17a0e3d

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
theorem _root_.solution (d : ℕ) : (possibleSpans K d).card ≤ 3 ^ (d * d) := by
  classical
  have h := Finset.card_image_le (f := spanCode (K := K) d)
    (s := (univ : Finset (Fin d → Fin d → Fin 3)))
  simpa [possibleSpans, Fintype.card_fun, pow_mul] using h
end ThreeSum.TernaryCoverRelations
