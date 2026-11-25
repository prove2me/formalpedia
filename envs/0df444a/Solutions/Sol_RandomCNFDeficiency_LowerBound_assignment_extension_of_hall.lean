-- Prove2me | solution 1 for RandomCNFDeficiency.LowerBound.assignment_extension_of_hall
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-25T20:13:34.444926+00:00
-- url     : https://prove2.me/submissions/cce70cf5-2220-46db-bc76-25b805688ae6

import Theorems.Thm_RandomCNFDeficiency_LowerBound_matching_of_external_hall
import Theorems.Thm_RandomCNFDeficiency_LowerBound_partial_assignment_of_clause_matching
noncomputable section
open RandomCNFDeficiency.LowerBound
set_option autoImplicit false
namespace AssignmentExtensionHallNext
theorem assignment_extension_of_hall {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (hH : ∀ L ⊆ H, L.card ≤ (neighborhood L \ S).card) (a : Assignment n) :
    ∃ b : Assignment n, (∀ i ∈ S, b i=a i) ∧ ∀ C ∈ H, SatisfiesClause b C := by
  obtain ⟨m,hm,hs⟩ := RandomCNFDeficiency.LowerBound.matching_of_external_hall H S hH
  obtain ⟨ρ,hρ,hn⟩ := RandomCNFDeficiency.LowerBound.partial_assignment_of_clause_matching H S m hm hs
  refine ⟨fun i => (ρ i).getD (a i),?_,?_⟩
  · intro i hi
    simp [hn i hi]
  · intro C hC
    obtain ⟨i,v,hi,hv⟩ := hρ C hC
    exact ⟨i,by simpa [hi] using hv⟩
end AssignmentExtensionHallNext

end
open RandomCNFDeficiency.LowerBound

set_option autoImplicit false

theorem solution {n : ℕ} (H : CNF n) (S : Finset (Fin n))
    (hH : ∀ L ⊆ H, L.card ≤ (neighborhood L \ S).card) (a : Assignment n) :
    ∃ b : Assignment n, (∀ i ∈ S, b i=a i) ∧ ∀ C ∈ H, SatisfiesClause b C := by
 exact AssignmentExtensionHallNext.assignment_extension_of_hall H S hH a