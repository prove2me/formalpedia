-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.pow_dvd_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:41.886085+00:00
-- url     : https://prove2.me/submissions/1fb5943d-b483-4f3d-a519-746b0c5fe5fc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open Polynomial
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (N ρ i : ℕ) (f : ℕ → ℕ → Polynomial ℂ) (hi : i ≤ N)
    (hf : ∀ l < i, ∃ i' < ρ, f l i' = -X) :
    (X : Polynomial ℂ) ^ i ∣ ∏ l ∈ Finset.range N, ∏ i' ∈ Finset.range ρ, f l i' := by
  have h1 : (X : Polynomial ℂ) ^ i = ∏ _l ∈ Finset.range i, (X : Polynomial ℂ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h1]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun l hl => ?_)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hi))
  obtain ⟨i', hi', he⟩ := hf l (Finset.mem_range.1 hl)
  have h2 : f l i' ∣ ∏ i' ∈ Finset.range ρ, f l i' := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi')
  rw [he] at h2
  exact dvd_trans (dvd_neg.2 dvd_rfl) h2
end PositivityTheory.Rg.Sw.SP
