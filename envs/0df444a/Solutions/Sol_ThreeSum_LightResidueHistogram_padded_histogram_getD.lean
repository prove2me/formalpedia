-- Prove2me | solution 1 for ThreeSum.LightResidueHistogram.padded_histogram_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:57.147818+00:00
-- url     : https://prove2.me/submissions/59caa2ad-50f8-48f5-a7e5-a8383c89bcaf

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Theorems.Thm_ThreeSum_LightResidueHistogram_signedHistogram_eq_count
import Theorems.Thm_ThreeSum_LightResidueHistogram_signed_count_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_padTo
import Theorems.Thm_ThreeSum_CyclicFold_vector_getD
import Theorems.Thm_ThreeSum_CyclicFold_vector_length
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff



set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidueHistogram
theorem _root_.solution {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap r : ℕ) :
    (padTo cap (vector p (signedHistogram p c values n))).getD r 0 =
      (count (fun i => residue p c (values i)) r n : ℤ) := by
  rw [← asPolynomial_coeff, asPolynomial_padTo, asPolynomial_coeff]
  by_cases hr : r < p
  · rw [vector_getD _ _ _ hr, signedHistogram_eq_count c values n r hr]
  · rw [List.getD_eq_default _ _ (by rw [vector_length]; omega)]
    rw [signed_count_zero (Nat.pos_of_ne_zero (NeZero.ne p)) c values n r (by omega)]
    rfl
end ThreeSum.LightResidueHistogram
