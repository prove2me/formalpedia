-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.exists_irreducible_candidate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:06.118814+00:00
-- url     : https://prove2.me/submissions/d8c36074-2117-4761-8734-43ef69621225

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_of_monic
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_exists_monic_irreducible


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (d : ℕ) (hd : 0<d) :
    ∃ a : Fin d → ZMod p, Irreducible (monicCandidate a) := by
  obtain ⟨f,hmon,hI,hdeg⟩ := exists_monic_irreducible p d hd
  refine ⟨fun i => f.coeff i.val,?_⟩
  rw [monicCandidate_of_monic hmon hdeg]
  exact hI
end ThreeSum.TernaryExtensionEncoding
