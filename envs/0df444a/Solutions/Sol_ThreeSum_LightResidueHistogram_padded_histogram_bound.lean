-- Prove2me | solution 1 for ThreeSum.LightResidueHistogram.padded_histogram_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:26:10.543422+00:00
-- url     : https://prove2.me/submissions/1dce02f6-52c7-4827-935d-5b96183ac99e

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Theorems.Thm_ThreeSum_LightResidueHistogram_padded_histogram_getD
import Theorems.Thm_ThreeSum_LightHistogram_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidueHistogram
theorem _root_.solution {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap : ℕ) :
    CoeffBound (padTo cap (vector p (signedHistogram p c values n))) (n : ℤ) := by
  intro r
  rw [padded_histogram_getD, abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast count_le (fun i => residue p c (values i)) r n
end ThreeSum.LightResidueHistogram
