-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.vectorPolynomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:03.462693+00:00
-- url     : https://prove2.me/submissions/96c69287-d3be-4692-963e-143e68792a02

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    (vectorPolynomial a).coeff i.val=a i := by
  simp only [vectorPolynomial,finsetSum_coeff,coeff_monomial,Fin.val_eq_val,
    Finset.sum_ite_eq',if_pos (Finset.mem_univ i)]
end ThreeSum.TernaryExtensionEncoding
