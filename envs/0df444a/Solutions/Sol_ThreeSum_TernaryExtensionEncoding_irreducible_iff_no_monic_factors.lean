-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.irreducible_iff_no_monic_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:54.5096+00:00
-- url     : https://prove2.me/submissions/e8e0afe6-bf2a-4da1-919b-f539ee7cbc0c

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_ThreeSum_TernaryExtensionRelations
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_degree
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_of_monic


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hdeg : f.natDegree=d) (hd : 0<d) :
    Irreducible f ↔ ∀ e, 0<e → e<d →
      ∀ (a : Fin e → ZMod p) (b : Fin (d-e) → ZMod p),
        monicCandidate a*monicCandidate b≠f := by
  constructor
  · intro hI e he hed a b hab
    rcases hI.2 hab.symm with hu | hu
    · have hz := natDegree_eq_zero_of_isUnit hu
      rw [monicCandidate_degree] at hz
      omega
    · have hz := natDegree_eq_zero_of_isUnit hu
      rw [monicCandidate_degree] at hz
      omega
  · intro h
    apply hf.irreducible_iff_natDegree.mpr
    refine ⟨?_,?_⟩
    · intro he
      rw [he,natDegree_one] at hdeg
      omega
    · intro g k hg hk hprod
      by_cases hz : g.natDegree=0
      · exact Or.inl hz
      by_cases hz' : k.natDegree=0
      · exact Or.inr hz'
      have hsum : g.natDegree+k.natDegree=d := by rw [← hdeg,← hprod,hg.natDegree_mul hk]
      have he : 0<g.natDegree := by omega
      have hed : g.natDegree<d := by omega
      have hkdeg : k.natDegree=d-g.natDegree := by omega
      exfalso
      apply h g.natDegree he hed (fun i => g.coeff i.val) (fun i => k.coeff i.val)
      rw [monicCandidate_of_monic hg rfl,monicCandidate_of_monic hk hkdeg,hprod]
end ThreeSum.TernaryExtensionEncoding
