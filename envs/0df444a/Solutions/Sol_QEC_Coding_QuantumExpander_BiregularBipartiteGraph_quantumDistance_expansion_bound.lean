-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.quantumDistance_expansion_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:55:02.878557+00:00
-- url     : https://prove2.me/submissions/c7338a54-4160-4353-a3db-7112f59c8f78

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_ofReal_left_expansion_le_extendedMinimumDistance
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_ofReal_right_expansion_le_extendedMinimumDistance
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_quantumDistance_eq_min_classicalDistances
import Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_extendedNatToENNReal_min

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
    (G : BiregularBipartiteGraph A B)
    {γA δA γB δB : Real}
    (hExpand : G.LeftRightExpanding γA δA γB δB)
    (hδA : δA < 1 / 2) (hδB : δB < 1 / 2) :
    ENNReal.ofReal
        (min (γA * Fintype.card A) (γB * Fintype.card B)) ≤
      extendedNatToENNReal
        (extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode G.hypergraphProductData).xCode
          (binaryCSSCode G.hypergraphProductData).zCode) := by
  have hLeft := ofReal_left_expansion_le_extendedMinimumDistance
    G hExpand.1 hδA
  have hRight := ofReal_right_expansion_le_extendedMinimumDistance
    G hExpand.2 hδB
  rw [quantumDistance_eq_min_classicalDistances,
    extendedNatToENNReal_min, ENNReal.ofReal_min]
  exact min_le_min hLeft hRight
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
