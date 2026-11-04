-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.monicCandidate_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:45.812545+00:00
-- url     : https://prove2.me/submissions/9ad3ad0e-c400-4185-b57a-7fad8340749d

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_monic
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_degree
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_coeff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hd : f.natDegree=d) :
    monicCandidate (fun i : Fin d => f.coeff i.val)=f := by
  ext k
  by_cases hk : k<d
  · simpa using monicCandidate_coeff (fun i : Fin d => f.coeff i.val) ⟨k,hk⟩
  · by_cases he : k=d
    · subst k
      have hc := (monicCandidate_monic (fun i : Fin d => f.coeff i.val)).coeff_natDegree
      rw [monicCandidate_degree] at hc
      rw [hc]
      simpa [hd] using hf.coeff_natDegree.symm
    · have hlt : d<k := by omega
      rw [coeff_eq_zero_of_natDegree_lt (by simpa [monicCandidate_degree] using hlt),
        coeff_eq_zero_of_natDegree_lt (by omega)]
end ThreeSum.TernaryExtensionEncoding
