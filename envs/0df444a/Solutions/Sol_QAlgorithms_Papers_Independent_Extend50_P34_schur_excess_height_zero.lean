-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P34.schur_excess_height_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:19:25.388666+00:00
-- url     : https://prove2.me/submissions/e9885877-93c9-4bad-b480-2d208bc63dd8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)
open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

open QAlgorithms.Papers.Independent.Extend50.P34 in
theorem solution
    (lambda : YoungDiagram) (d : ℕ) (hheight : d < lambda.colLen 0) :
    extendedSchurPolynomial d lambda = 0 := by
  simp [extendedSchurPolynomial, not_le.mpr hheight]
