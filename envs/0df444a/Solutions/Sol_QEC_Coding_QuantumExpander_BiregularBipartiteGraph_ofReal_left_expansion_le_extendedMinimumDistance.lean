-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ofReal_left_expansion_le_extendedMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:50:02.472665+00:00
-- url     : https://prove2.me/submissions/3021ee74-52c3-46c0-bafa-1a219992fcf5

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_extendedNatToENNReal_mono
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_ceil_left_expansion_le_extendedMinimumDistance

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
    ENNReal.ofReal (γ * Fintype.card A) ≤
      extendedNatToENNReal
        (extendedMinimumDistance (firstCode G.hypergraphProductData)) := by
  calc
    ENNReal.ofReal (γ * Fintype.card A) ≤
        (Nat.ceil (γ * Fintype.card A) : ENNReal) := by
      rw [ENNReal.ofReal_le_natCast]
      exact Nat.le_ceil _
    _ = extendedNatToENNReal
        (Nat.ceil (γ * Fintype.card A) : WithTop Nat) := by rfl
    _ ≤ extendedNatToENNReal
        (extendedMinimumDistance (firstCode G.hypergraphProductData)) :=
      extendedNatToENNReal_mono
        (ceil_left_expansion_le_extendedMinimumDistance G hExpand hδ)
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
