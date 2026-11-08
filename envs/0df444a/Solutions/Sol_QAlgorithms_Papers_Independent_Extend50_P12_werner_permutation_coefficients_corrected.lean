-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P12.werner_permutation_coefficients_corrected
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:28:26.008898+00:00
-- url     : https://prove2.me/submissions/5fb64382-f7be-4027-829b-158d81e98765

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12

noncomputable section

open scoped BigOperators Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Extend50.P12 in
theorem solution
    (d : ℕ) (hd : 0 < d) (c : Fin 6 → ℝ)
    (hpositive : (wernerFromCoefficients d c).PosSemidef)
    (htrace : Matrix.trace (wernerFromCoefficients d c) = 1) :
    wernerFromCoefficients d c =
      ∑ j : Fin 6, correctedPermutationCoefficients c j • wernerPermutations d j := by
  unfold wernerFromCoefficients wernerBasis correctedPermutationCoefficients
  simp only [Fin.sum_univ_six, Matrix.cons_val]
  module

end
