-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P07.schur_complement
-- status  : ACCEPTED   (prove)
-- author  : @Mceppaglia
-- created : 2026-11-20T12:46:26.056807+00:00
-- url     : https://prove2.me/submissions/f705dec2-efe1-46db-95da-4b346da90a4d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

set_option autoImplicit false

noncomputable section

open QAlgorithms.Papers.Independent.Intakenext100.P07
open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- The published statement includes hM; the lower-right Schur criterion only needs hN.
set_option linter.unusedVariables false in
theorem solution {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty I] [Nonempty J]
    (M : paperMat I) (N : paperMat J) (X : Matrix I J ℂ)
    (hM : M.PosDef) (hN : N.PosDef) :
    (Matrix.fromBlocks M X Xᴴ N).PosSemidef ↔ paperBelow (X * N⁻¹ * Xᴴ) M := by
  let : Invertible N := hN.isUnit.invertible
  exact Matrix.PosDef.fromBlocks₂₂ M X hN

end
