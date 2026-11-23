-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_exists_nodes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:23.664679+00:00
-- url     : https://prove2.me/submissions/7a71e113-aadb-434b-80b5-5b3267286dc9

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (E : Set ℂ) (hE : E.Finite) (k : ℕ) :
    ∃ S : Finset ℂ, S.card = k + 1 ∧ ∀ c ∈ S, c ∉ E := by
  obtain ⟨S, hS, hcard⟩ := hE.infinite_compl.exists_subset_card_eq (k + 1)
  exact ⟨S, hcard, fun c hc => hS hc⟩
end ReciprocityTheory.MultiplicativeHeights
