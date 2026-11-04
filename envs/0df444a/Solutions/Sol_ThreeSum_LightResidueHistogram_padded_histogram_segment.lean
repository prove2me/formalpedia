-- Prove2me | solution 1 for ThreeSum.LightResidueHistogram.padded_histogram_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:04.3998+00:00
-- url     : https://prove2.me/submissions/88424c85-f3be-4bec-bdca-4f7c4d632de5

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Theorems.Thm_ThreeSum_LightResidueHistogram_padded_histogram_getD
import Theorems.Thm_ThreeSum_CyclicFold_padTo_length
import Theorems.Thm_ThreeSum_CyclicFold_vector_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidueHistogram
theorem _root_.solution {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) {n cap dst : ℕ} {μ : ℕ → ℤ}
    (hcap : p ≤ cap)
    (hout : ∀ r < cap, μ (dst + r) =
      (count (fun i => residue p c (values i)) r n : ℤ)) :
    Seg μ dst (padTo cap (vector p (signedHistogram p c values n))) := by
  intro r hr
  have hlen : (padTo cap (vector p (signedHistogram p c values n))).length = cap := by
    apply padTo_length
    rw [vector_length]
    exact hcap
  have hrcap : r < cap := by omega
  rw [← List.getD_eq_getElem _ 0 hr, padded_histogram_getD]
  exact hout r hrcap
end ThreeSum.LightResidueHistogram
