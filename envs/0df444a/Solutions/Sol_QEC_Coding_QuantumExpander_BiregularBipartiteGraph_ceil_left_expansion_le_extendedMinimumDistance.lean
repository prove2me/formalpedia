-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ceil_left_expansion_le_extendedMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:48:01.368703+00:00
-- url     : https://prove2.me/submissions/48eb4a65-6d3f-4584-b44d-2ffcbe97535b

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_left_classical_codeword_weight_ge
import Theorems.Thm_QEC_Coding_HypergraphProduct_le_finitePredicateMinimum


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace QEC.Coding.QuantumExpander.BiregularBipartiteGraph
theorem _root_.solution
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2) :
    (Nat.ceil (γ * Fintype.card A) : WithTop Nat) ≤
      extendedMinimumDistance (firstCode G.hypergraphProductData) := by
  classical
  rw [extendedMinimumDistance]
  apply le_finitePredicateMinimum
  intro x hx
  have hReal := left_classical_codeword_weight_ge G hExpand hδ x hx.1 hx.2
  have hNat : Nat.ceil (γ * Fintype.card A) ≤ HammingWeight x :=
    Nat.ceil_le.mpr hReal
  exact_mod_cast hNat
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
