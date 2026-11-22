-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminalFactor_induce_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:42.810489+00:00
-- url     : https://prove2.me/submissions/4fc85aae-6480-4553-b10c-e6250a32efcf

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
import Theorems.Thm_Paper_Hypergraph_log_nat_mono
import Theorems.Thm_Paper_Hypergraph_independenceNumber_induce_mono
import Theorems.Thm_Paper_Hypergraph_induce_induce
import Theorems.Thm_Paper_Hypergraph_structure_hereditary


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (Q : Finset ℕ) {R T : Finset ℕ}
    (hTR : T ⊆ R) : (H.induce Q).twoTerminalFactor T ≤ H.twoTerminalFactor R := by
  apply min_le_min
  · rw [H.induce_induce]
    have h := log_nat_mono (H.independenceNumber_induce_mono (inter_subset_right.trans hTR : Q ∩ T ⊆ R))
    linarith
  · have h : ((H.induce Q).degeneracy : ℝ) ≤ H.degeneracy := by
      exact_mod_cast (H.structure_hereditary Q).1
    linarith
end Paper.Hypergraph
