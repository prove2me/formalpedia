-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminal_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:36.482943+00:00
-- url     : https://prove2.me/submissions/eda1eb19-52d6-48a2-979b-4ebc24005e77

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
import Theorems.Thm_Paper_Hypergraph_twoTerminal_degeneracy_rounding
import Theorems.Thm_Paper_Hypergraph_twoTerminal_independence_rounding


set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution : TwoTerminalRounding := by
  intro H A B x hA hB hx
  let R := H.vertices.filter (fun v => x v ≠ 0)
  by_cases h : 8 + 4 * Real.log ((H.induce R).independenceNumber : ℝ) ≤ (6 * H.degeneracy : ℝ)
  · dsimp only [R] at h
    obtain ⟨S, hS, hsep, hcost⟩ := H.twoTerminal_independence_rounding hA hB hx
    refine ⟨S, hS, hsep, ?_⟩
    simpa only [twoTerminalFactor, min_eq_left h] using hcost
  · dsimp only [R] at h
    obtain ⟨S, hS, hsep, hcost⟩ := H.twoTerminal_degeneracy_rounding hA hB hx
    refine ⟨S, hS, hsep, ?_⟩
    simpa only [twoTerminalFactor, min_eq_right (le_of_not_ge h)] using hcost
end Paper.Hypergraph
