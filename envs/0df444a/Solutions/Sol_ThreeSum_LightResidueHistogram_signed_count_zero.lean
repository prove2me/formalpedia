-- Prove2me | solution 1 for ThreeSum.LightResidueHistogram.signed_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:09.419056+00:00
-- url     : https://prove2.me/submissions/a915508f-63aa-490c-b46b-a677d4366299

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Theorems.Thm_ThreeSum_LightResidues_residue_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidueHistogram
theorem _root_.solution {p : ℕ} (hp : 0 < p)
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : p ≤ r) :
    count (fun i => residue p c (values i)) r n = 0 := by
  unfold count
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i hi heq
  change residue p c (values i) = r at heq
  have h := residue_lt hp c (values i)
  omega
end ThreeSum.LightResidueHistogram
