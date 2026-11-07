-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.ofReal_right_expansion_le_extendedMinimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:52:21.304368+00:00
-- url     : https://prove2.me/submissions/b3231ffe-20ba-4777-9ff3-d8285e4a04cf

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_ofReal_left_expansion_le_extendedMinimumDistance

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
    (hExpand : G.RightExpanding γ δ) (hδ : δ < 1 / 2) :
    ENNReal.ofReal (γ * Fintype.card B) ≤
      extendedNatToENNReal
        (extendedMinimumDistance (firstTransposeCode G.hypergraphProductData)) := by
  exact ofReal_left_expansion_le_extendedMinimumDistance G.swap hExpand hδ
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
