-- Prove2me | solution 1 for ThreeSum.RawIncidences.witnesses_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:07.848373+00:00
-- url     : https://prove2.me/submissions/09e52fbe-20f8-4809-a36c-05015f025804

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_mem_witnesses
import Theorems.Thm_ThreeSum_RawIncidences_witness_projection_injective
import Theorems.Thm_ThreeSum_GlobalEncoding_representations_card_bound


set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).card ≤ representationCap h J := by
  calc
    _ ≤ (representations h J (b % P) (c % P + d)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Witness h J => List.ofFn w.1)
      · intro w hw
        exact (mem_witnesses.mp hw).1
      · exact witness_projection_injective hP hguard
    _ ≤ _ := representations_card_bound h J (b % P) (c % P + d)
end ThreeSum.RawIncidences
